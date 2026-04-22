using System;
using System.Diagnostics;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using ILGPU;
using ILGPU.Runtime;
using ILGPU.Runtime.Cuda;

class Program
{
    // Full charset: lower + upper + digits + specials — always used for both modes
    static readonly string CHARSET =
        "abcdefghijklmnopqrstuvwxyz" +
        "ABCDEFGHIJKLMNOPQRSTUVWXYZ" +
        "0123456789" +
        "!@#$%^&*()-_=+[]{};:,.<>?";

    const int MAX_LENGTH = 7;

    static long          attempts  = 0;
    static volatile bool found     = false;
    static string        lastGuess = "";
    static CancellationTokenSource cts = new();

    // ── Kernel: Standard brute-force ─────────────────────────────────────────
    static void KernelStandard(
        Index1D         index,
        ArrayView<byte> charset,
        ArrayView<byte> password,
        ArrayView<int>  foundFlag,
        ArrayView<long> result,
        ArrayView<long> powers,
        int  baseLen,
        int  length,
        long offset)
    {
        long globalIdx = index + offset;

        byte c0 = charset[(int)(globalIdx                  % baseLen)];
        byte c1 = charset[(int)(globalIdx / powers[1] % baseLen)];
        byte c2 = charset[(int)(globalIdx / powers[2] % baseLen)];
        byte c3 = charset[(int)(globalIdx / powers[3] % baseLen)];
        byte c4 = charset[(int)(globalIdx / powers[4] % baseLen)];
        byte c5 = charset[(int)(globalIdx / powers[5] % baseLen)];
        byte c6 = charset[(int)(globalIdx / powers[6] % baseLen)];

        if (length > 6 && c6 != password[6]) return;
        if (length > 5 && c5 != password[5]) return;
        if (length > 4 && c4 != password[4]) return;
        if (length > 3 && c3 != password[3]) return;
        if (length > 2 && c2 != password[2]) return;
        if (length > 1 && c1 != password[1]) return;
        if (              c0 != password[0]) return;

        Atomic.Exchange(ref foundFlag[0], 1);
        result[0] = globalIdx;
    }

    // ── Kernel: MD5 hash crack (1–7 char input, full charset) ────────────────
    // MD5 pads the message to a 512-bit block. For short inputs everything fits
    // in the first two 32-bit words (m0, m1); m2..m13 are always 0 for ≤7 bytes.
    // m14 holds the bit-length (length × 8) and m15 is always 0.
    //
    // Padding per length (0x80 byte immediately follows last message byte):
    //   len 1: m0 = b0 | 0x80<<8                                   m14 =  8
    //   len 2: m0 = b0 | b1<<8 | 0x80<<16                          m14 = 16
    //   len 3: m0 = b0 | b1<<8 | b2<<16 | 0x80<<24                 m14 = 24
    //   len 4: m0 = b0 | b1<<8 | b2<<16 | b3<<24  m1 = 0x00000080  m14 = 32
    //   len 5: m0 = b0 | b1<<8 | b2<<16 | b3<<24  m1 = b4 | 0x80<<8        m14 = 40
    //   len 6: m0 = b0 | b1<<8 | b2<<16 | b3<<24  m1 = b4|b5<<8|0x80<<16   m14 = 48
    //   len 7: m0 = b0 | b1<<8 | b2<<16 | b3<<24  m1 = b4|b5<<8|b6<<16|0x80<<24 m14 = 56
    static uint RL(uint x, int n) => (x << n) | (x >> (32 - n));

    static void KernelMD5(
        Index1D         index,
        ArrayView<byte> charset,
        ArrayView<int>  targetWords,   // 4 × LE uint32 words of the target digest
        ArrayView<int>  foundFlag,
        ArrayView<long> result,
        ArrayView<long> powers,
        int  baseLen,
        int  length,
        long offset)
    {
        if (foundFlag[0] == 1) return;
        long gi = index + offset;

        // ── Decode candidate characters from linear index ─────────────────
        byte b0 = length > 0 ? charset[(int)(gi                  % baseLen)] : (byte)0;
        byte b1 = length > 1 ? charset[(int)(gi / powers[1] % baseLen)]      : (byte)0;
        byte b2 = length > 2 ? charset[(int)(gi / powers[2] % baseLen)]      : (byte)0;
        byte b3 = length > 3 ? charset[(int)(gi / powers[3] % baseLen)]      : (byte)0;
        byte b4 = length > 4 ? charset[(int)(gi / powers[4] % baseLen)]      : (byte)0;
        byte b5 = length > 5 ? charset[(int)(gi / powers[5] % baseLen)]      : (byte)0;
        byte b6 = length > 6 ? charset[(int)(gi / powers[6] % baseLen)]      : (byte)0;

        // ── Build message words m0 and m1 based on length ─────────────────
        // m2..m13 are always 0 for inputs ≤ 7 bytes (fits in 8 bytes / 2 words).
        uint m0, m1;
        uint m14 = (uint)(length * 8);   // bit-length

        if (length <= 3)
        {
            // All message bytes and the pad byte fit inside m0 alone
            m1 = 0u;
            if      (length == 1) m0 = (uint)b0 | 0x00008000u;
            else if (length == 2) m0 = (uint)b0 | ((uint)b1 << 8) | 0x00800000u;
            else                  m0 = (uint)b0 | ((uint)b1 << 8) | ((uint)b2 << 16) | 0x80000000u;
        }
        else
        {
            // m0 is fully occupied by bytes 0–3; pad goes into m1
            m0 = (uint)b0 | ((uint)b1 << 8) | ((uint)b2 << 16) | ((uint)b3 << 24);
            if      (length == 4) m1 = 0x00000080u;
            else if (length == 5) m1 = (uint)b4 | 0x00008000u;
            else if (length == 6) m1 = (uint)b4 | ((uint)b5 << 8) | 0x00800000u;
            else                  m1 = (uint)b4 | ((uint)b5 << 8) | ((uint)b6 << 16) | 0x80000000u;
        }

        // ── MD5 compression ───────────────────────────────────────────────
        uint a = 0x67452301u, b = 0xefcdab89u, c = 0x98badcfeu, d = 0x10325476u;
        uint f, nv;

        // Round 1 — F(b,c,d)=(b&c)|(~b&d), g=i, shifts {7,12,17,22}
        f=(b&c)|(~b&d); nv=RL(a+f+m0 +0xd76aa478u, 7)+b; a=d;d=c;c=b;b=nv;
        f=(b&c)|(~b&d); nv=RL(a+f+m1 +0xe8c7b756u,12)+b; a=d;d=c;c=b;b=nv;
        f=(b&c)|(~b&d); nv=RL(a+f+0  +0x242070dbu,17)+b; a=d;d=c;c=b;b=nv;
        f=(b&c)|(~b&d); nv=RL(a+f+0  +0xc1bdceeeu,22)+b; a=d;d=c;c=b;b=nv;
        f=(b&c)|(~b&d); nv=RL(a+f+0  +0xf57c0fafu, 7)+b; a=d;d=c;c=b;b=nv;
        f=(b&c)|(~b&d); nv=RL(a+f+0  +0x4787c62au,12)+b; a=d;d=c;c=b;b=nv;
        f=(b&c)|(~b&d); nv=RL(a+f+0  +0xa8304613u,17)+b; a=d;d=c;c=b;b=nv;
        f=(b&c)|(~b&d); nv=RL(a+f+0  +0xfd469501u,22)+b; a=d;d=c;c=b;b=nv;
        f=(b&c)|(~b&d); nv=RL(a+f+0  +0x698098d8u, 7)+b; a=d;d=c;c=b;b=nv;
        f=(b&c)|(~b&d); nv=RL(a+f+0  +0x8b44f7afu,12)+b; a=d;d=c;c=b;b=nv;
        f=(b&c)|(~b&d); nv=RL(a+f+0  +0xffff5bb1u,17)+b; a=d;d=c;c=b;b=nv;
        f=(b&c)|(~b&d); nv=RL(a+f+0  +0x895cd7beu,22)+b; a=d;d=c;c=b;b=nv;
        f=(b&c)|(~b&d); nv=RL(a+f+0  +0x6b901122u, 7)+b; a=d;d=c;c=b;b=nv;
        f=(b&c)|(~b&d); nv=RL(a+f+0  +0xfd987193u,12)+b; a=d;d=c;c=b;b=nv;
        f=(b&c)|(~b&d); nv=RL(a+f+m14+0xa679438eu,17)+b; a=d;d=c;c=b;b=nv;
        f=(b&c)|(~b&d); nv=RL(a+f+0  +0x49b40821u,22)+b; a=d;d=c;c=b;b=nv;

        // Round 2 — G(b,c,d)=(d&b)|(~d&c), g=(5i+1)%16, shifts {5,9,14,20}
        f=(d&b)|(~d&c); nv=RL(a+f+m1 +0xf61e2562u, 5)+b; a=d;d=c;c=b;b=nv;
        f=(d&b)|(~d&c); nv=RL(a+f+0  +0xc040b340u, 9)+b; a=d;d=c;c=b;b=nv;
        f=(d&b)|(~d&c); nv=RL(a+f+0  +0x265e5a51u,14)+b; a=d;d=c;c=b;b=nv;
        f=(d&b)|(~d&c); nv=RL(a+f+m0 +0xe9b6c7aau,20)+b; a=d;d=c;c=b;b=nv;
        f=(d&b)|(~d&c); nv=RL(a+f+0  +0xd62f105du, 5)+b; a=d;d=c;c=b;b=nv;
        f=(d&b)|(~d&c); nv=RL(a+f+0  +0x02441453u, 9)+b; a=d;d=c;c=b;b=nv;
        f=(d&b)|(~d&c); nv=RL(a+f+0  +0xd8a1e681u,14)+b; a=d;d=c;c=b;b=nv;
        f=(d&b)|(~d&c); nv=RL(a+f+0  +0xe7d3fbc8u,20)+b; a=d;d=c;c=b;b=nv;
        f=(d&b)|(~d&c); nv=RL(a+f+0  +0x21e1cde6u, 5)+b; a=d;d=c;c=b;b=nv;
        f=(d&b)|(~d&c); nv=RL(a+f+m14+0xc33707d6u, 9)+b; a=d;d=c;c=b;b=nv;
        f=(d&b)|(~d&c); nv=RL(a+f+0  +0xf4d50d87u,14)+b; a=d;d=c;c=b;b=nv;
        f=(d&b)|(~d&c); nv=RL(a+f+0  +0x455a14edu,20)+b; a=d;d=c;c=b;b=nv;
        f=(d&b)|(~d&c); nv=RL(a+f+0  +0xa9e3e905u, 5)+b; a=d;d=c;c=b;b=nv;
        f=(d&b)|(~d&c); nv=RL(a+f+0  +0xfcefa3f8u, 9)+b; a=d;d=c;c=b;b=nv;
        f=(d&b)|(~d&c); nv=RL(a+f+0  +0x676f02d9u,14)+b; a=d;d=c;c=b;b=nv;
        f=(d&b)|(~d&c); nv=RL(a+f+0  +0x8d2a4c8au,20)+b; a=d;d=c;c=b;b=nv;

        // Round 3 — H(b,c,d)=b^c^d, g=(3i+5)%16, shifts {4,11,16,23}
        f=b^c^d; nv=RL(a+f+0  +0xfffa3942u, 4)+b; a=d;d=c;c=b;b=nv;
        f=b^c^d; nv=RL(a+f+0  +0x8771f681u,11)+b; a=d;d=c;c=b;b=nv;
        f=b^c^d; nv=RL(a+f+0  +0x6d9d6122u,16)+b; a=d;d=c;c=b;b=nv;
        f=b^c^d; nv=RL(a+f+m14+0xfde5380cu,23)+b; a=d;d=c;c=b;b=nv;
        f=b^c^d; nv=RL(a+f+m1 +0xa4beea44u, 4)+b; a=d;d=c;c=b;b=nv;
        f=b^c^d; nv=RL(a+f+0  +0x4bdecfa9u,11)+b; a=d;d=c;c=b;b=nv;
        f=b^c^d; nv=RL(a+f+0  +0xf6bb4b60u,16)+b; a=d;d=c;c=b;b=nv;
        f=b^c^d; nv=RL(a+f+0  +0xbebfbc70u,23)+b; a=d;d=c;c=b;b=nv;
        f=b^c^d; nv=RL(a+f+0  +0x289b7ec6u, 4)+b; a=d;d=c;c=b;b=nv;
        f=b^c^d; nv=RL(a+f+m0 +0xeaa127fau,11)+b; a=d;d=c;c=b;b=nv;
        f=b^c^d; nv=RL(a+f+0  +0xd4ef3085u,16)+b; a=d;d=c;c=b;b=nv;
        f=b^c^d; nv=RL(a+f+0  +0x04881d05u,23)+b; a=d;d=c;c=b;b=nv;
        f=b^c^d; nv=RL(a+f+0  +0xd9d4d039u, 4)+b; a=d;d=c;c=b;b=nv;
        f=b^c^d; nv=RL(a+f+0  +0xe6db99e5u,11)+b; a=d;d=c;c=b;b=nv;
        f=b^c^d; nv=RL(a+f+0  +0x1fa27cf8u,16)+b; a=d;d=c;c=b;b=nv;
        f=b^c^d; nv=RL(a+f+0  +0xc4ac5665u,23)+b; a=d;d=c;c=b;b=nv;

        // Round 4 — I(b,c,d)=c^(b|~d), g=(7i)%16, shifts {6,10,15,21}
        f=c^(b|~d); nv=RL(a+f+m0 +0xf4292244u, 6)+b; a=d;d=c;c=b;b=nv;
        f=c^(b|~d); nv=RL(a+f+0  +0x432aff97u,10)+b; a=d;d=c;c=b;b=nv;
        f=c^(b|~d); nv=RL(a+f+m14+0xab9423a7u,15)+b; a=d;d=c;c=b;b=nv;
        f=c^(b|~d); nv=RL(a+f+0  +0xfc93a039u,21)+b; a=d;d=c;c=b;b=nv;
        f=c^(b|~d); nv=RL(a+f+0  +0x655b59c3u, 6)+b; a=d;d=c;c=b;b=nv;
        f=c^(b|~d); nv=RL(a+f+0  +0x8f0ccc92u,10)+b; a=d;d=c;c=b;b=nv;
        f=c^(b|~d); nv=RL(a+f+0  +0xffeff47du,15)+b; a=d;d=c;c=b;b=nv;
        f=c^(b|~d); nv=RL(a+f+m1 +0x85845dd1u,21)+b; a=d;d=c;c=b;b=nv;
        f=c^(b|~d); nv=RL(a+f+0  +0x6fa87e4fu, 6)+b; a=d;d=c;c=b;b=nv;
        f=c^(b|~d); nv=RL(a+f+0  +0xfe2ce6e0u,10)+b; a=d;d=c;c=b;b=nv;
        f=c^(b|~d); nv=RL(a+f+0  +0xa3014314u,15)+b; a=d;d=c;c=b;b=nv;
        f=c^(b|~d); nv=RL(a+f+0  +0x4e0811a1u,21)+b; a=d;d=c;c=b;b=nv;
        f=c^(b|~d); nv=RL(a+f+0  +0xf7537e82u, 6)+b; a=d;d=c;c=b;b=nv;
        f=c^(b|~d); nv=RL(a+f+0  +0xbd3af235u,10)+b; a=d;d=c;c=b;b=nv;
        f=c^(b|~d); nv=RL(a+f+0  +0x2ad7d2bbu,15)+b; a=d;d=c;c=b;b=nv;
        f=c^(b|~d); nv=RL(a+f+0  +0xeb86d391u,21)+b; a=d;d=c;c=b;b=nv;

        // ── Final hash words ──────────────────────────────────────────────
        uint h0 = a + 0x67452301u;
        uint h1 = b + 0xefcdab89u;
        uint h2 = c + 0x98badcfeu;
        uint h3 = d + 0x10325476u;

        if ((int)h0 != targetWords[0]) return;
        if ((int)h1 != targetWords[1]) return;
        if ((int)h2 != targetWords[2]) return;
        if ((int)h3 != targetWords[3]) return;

        Atomic.Exchange(ref foundFlag[0], 1);
        result[0] = gi;
    }

    // ── Monitor thread ────────────────────────────────────────────────────────
    static void Monitor(long total, Stopwatch sw, CancellationToken token)
    {
        while (!found && !token.IsCancellationRequested)
        {
            Thread.Sleep(200);
            long     current  = Interlocked.Read(ref attempts);
            double   elapsed  = sw.Elapsed.TotalSeconds;
            long     speed    = elapsed > 0 ? (long)(current / elapsed) : 0;
            double   progress = (double)current / total * 100;
            double   eta      = speed > 0 ? (total - current) / (double)speed : 0;
            TimeSpan etaT     = TimeSpan.FromSeconds(eta);
            Console.Write(
                $"\r[{progress,6:F2}%] {current:N0} tries | {speed:N0}/s | ETA: {etaT.Minutes:D2}:{etaT.Seconds:D2} | Last: {lastGuess,-20}"
            );
        }
    }

    static void Main()
    {
        Console.CancelKeyPress += (s, e) =>
        {
            Console.WriteLine("\nStopping...");
            cts.Cancel();
            e.Cancel = true;
        };

        byte[] charsetBytes = CHARSET.Select(c => (byte)c).ToArray();
        int    baseLen      = charsetBytes.Length;

        // ── Menu ──────────────────────────────────────────────────────────────
        Console.WriteLine("Select mode:");
        Console.WriteLine($"1. Brute-force password  (up to {MAX_LENGTH} chars, full charset)");
        Console.WriteLine($"2. MD5 crack             (1–{MAX_LENGTH} chars, full charset)");
        Console.Write("\nChoice: ");
        string choice = Console.ReadLine() ?? "";

        const int BATCH = 200_000_000;

        using var context = Context.CreateDefault();
        Accelerator accel = null!;
        try
        {
            CudaDevice? cuda = context.Devices.OfType<CudaDevice>().FirstOrDefault();
            if (cuda != null) accel = cuda.CreateAccelerator(context);
        }
        catch { }

        if (accel == null)
        {
            Console.WriteLine("CUDA not found. Using CPU fallback.");
            accel = context.GetPreferredDevice(preferCPU: true).CreateAccelerator(context);
        }

        // Powers array covers indices 0–6 for up to 7-char candidates
        long[] powersHost = new long[7];
        powersHost[0] = 1;
        for (int i = 1; i < 7; i++) powersHost[i] = powersHost[i - 1] * baseLen;

        using (accel)
        {
            if (choice == "1")
            {
                // ── MODE 1: Standard brute-force, full charset ─────────────────
                Console.Write($"\nEnter password to crack (max {MAX_LENGTH} chars): ");
                string passwordStr = Console.ReadLine() ?? "";
                if (passwordStr.Length == 0 || passwordStr.Length > MAX_LENGTH)
                { Console.WriteLine($"Password must be 1–{MAX_LENGTH} characters."); return; }

                byte[] passwordBytes = passwordStr.Select(c => (byte)c).ToArray();
                long   combinations  = (long)Math.Pow(baseLen, passwordBytes.Length);

                Console.WriteLine($"\nCharset : {baseLen} characters");
                Console.WriteLine($"Length  : {passwordBytes.Length} characters");
                Console.WriteLine($"Total   : {combinations:N0} combinations");

                var kernelStd = accel.LoadAutoGroupedStreamKernel<
                    Index1D, ArrayView<byte>, ArrayView<byte>,
                    ArrayView<int>, ArrayView<long>, ArrayView<long>,
                    int, int, long>(KernelStandard);

                using var dCharset  = accel.Allocate1D<byte>(charsetBytes.Length);
                using var dPassword = accel.Allocate1D<byte>(passwordBytes.Length);
                using var dPowers   = accel.Allocate1D<long>(7);
                dCharset.CopyFromCPU(charsetBytes);
                dPassword.CopyFromCPU(passwordBytes);
                dPowers.CopyFromCPU(powersHost);

                using var dFoundA  = accel.Allocate1D<int>(1);
                using var dResultA = accel.Allocate1D<long>(1);
                using var dFoundB  = accel.Allocate1D<int>(1);
                using var dResultB = accel.Allocate1D<long>(1);
                int[] hFA = new int[1]; long[] hRA = new long[1];
                int[] hFB = new int[1]; long[] hRB = new long[1];
                dFoundA.MemSetToZero(); dResultA.MemSetToZero();
                dFoundB.MemSetToZero(); dResultB.MemSetToZero();

                void LaunchStd(int size, MemoryBuffer1D<int,Stride1D.Dense> dF,
                                         MemoryBuffer1D<long,Stride1D.Dense> dR, long off)
                    => kernelStd((Index1D)size,
                        dCharset.View, dPassword.View, dF.View, dR.View, dPowers.View,
                        baseLen, passwordBytes.Length, off);

                string DecodeStd(long idx)
                {
                    char[] g = new char[passwordBytes.Length]; long t = idx;
                    for (int i = 0; i < g.Length; i++) { g[i]=(char)charsetBytes[t%baseLen]; t/=baseLen; }
                    return new string(g);
                }

                RunDoubleBuffer(accel, combinations, BATCH,
                    LaunchStd, DecodeStd,
                    dFoundA, dResultA, dFoundB, dResultB, hFA, hRA, hFB, hRB);
            }
            else if (choice == "2")
            {
                // ── MODE 2: MD5 crack, variable length 1–7, full charset ────────
                Console.Write($"\nEnter password length to crack (1–{MAX_LENGTH}): ");
                if (!int.TryParse(Console.ReadLine(), out int md5Len) || md5Len < 1 || md5Len > MAX_LENGTH)
                { Console.WriteLine($"Length must be between 1 and {MAX_LENGTH}."); return; }

                Console.Write("Enter MD5 hash to crack (32 hex chars): ");
                string hexHash = (Console.ReadLine() ?? "").Trim().ToLowerInvariant();
                if (hexHash.Length != 32 || !hexHash.All(ch => "0123456789abcdef".Contains(ch)))
                { Console.WriteLine("Invalid MD5 hash (need exactly 32 hex characters)."); return; }

                byte[] hashBytes = Convert.FromHexString(hexHash);

                // 16 bytes → 4 little-endian uint32 words stored as int[] for ILGPU
                int[] targetWordsHost = new int[4];
                for (int i = 0; i < 4; i++)
                    targetWordsHost[i] = (int)(
                          (uint)hashBytes[i * 4]
                        | ((uint)hashBytes[i * 4 + 1] <<  8)
                        | ((uint)hashBytes[i * 4 + 2] << 16)
                        | ((uint)hashBytes[i * 4 + 3] << 24));

                long combinations = (long)Math.Pow(baseLen, md5Len);

                Console.WriteLine($"\nCharset : {baseLen} characters");
                Console.WriteLine($"Length  : {md5Len} characters");
                Console.WriteLine($"Target  : {hexHash}");
                Console.WriteLine($"Total   : {combinations:N0} combinations");

                var kernelMD5 = accel.LoadAutoGroupedStreamKernel<
                    Index1D,
                    ArrayView<byte>, ArrayView<int>, ArrayView<int>,
                    ArrayView<long>, ArrayView<long>, int, int, long>(KernelMD5);

                using var dCharset     = accel.Allocate1D<byte>(charsetBytes.Length);
                using var dTargetWords = accel.Allocate1D<int>(4);
                using var dPowers      = accel.Allocate1D<long>(7);
                dCharset.CopyFromCPU(charsetBytes);
                dTargetWords.CopyFromCPU(targetWordsHost);
                dPowers.CopyFromCPU(powersHost);

                using var dFoundA  = accel.Allocate1D<int>(1);
                using var dResultA = accel.Allocate1D<long>(1);
                using var dFoundB  = accel.Allocate1D<int>(1);
                using var dResultB = accel.Allocate1D<long>(1);
                int[] hFA = new int[1]; long[] hRA = new long[1];
                int[] hFB = new int[1]; long[] hRB = new long[1];
                dFoundA.MemSetToZero(); dResultA.MemSetToZero();
                dFoundB.MemSetToZero(); dResultB.MemSetToZero();

                void LaunchMD5(int size, MemoryBuffer1D<int, Stride1D.Dense> dF,
                                          MemoryBuffer1D<long,Stride1D.Dense> dR, long off)
                    => kernelMD5((Index1D)size,
                        dCharset.View, dTargetWords.View, dF.View, dR.View,
                        dPowers.View, baseLen, md5Len, off);

                string DecodeMD5(long idx)
                {
                    char[] g = new char[md5Len]; long t = idx;
                    for (int i = 0; i < md5Len; i++) { g[i]=(char)charsetBytes[t%baseLen]; t/=baseLen; }
                    return new string(g);
                }

                RunDoubleBuffer(accel, combinations, BATCH,
                    LaunchMD5, DecodeMD5,
                    dFoundA, dResultA, dFoundB, dResultB, hFA, hRA, hFB, hRB);
            }
            else
            {
                Console.WriteLine("Invalid choice. Please enter 1 or 2.");
            }
        }
    }

    // ── Shared double-buffer dispatch loop ────────────────────────────────────
    static void RunDoubleBuffer(
        Accelerator accel,
        long total, int BATCH,
        Action<int, MemoryBuffer1D<int,Stride1D.Dense>, MemoryBuffer1D<long,Stride1D.Dense>, long> launch,
        Func<long, string> decode,
        MemoryBuffer1D<int,Stride1D.Dense>  dFoundA, MemoryBuffer1D<long,Stride1D.Dense> dResultA,
        MemoryBuffer1D<int,Stride1D.Dense>  dFoundB, MemoryBuffer1D<long,Stride1D.Dense> dResultB,
        int[] hFA, long[] hRA, int[] hFB, long[] hRB)
    {
        var sw = Stopwatch.StartNew();
        Task.Run(() => Monitor(total, sw, cts.Token));

        int firstSize = (int)Math.Min(BATCH, total);
        launch(firstSize, dFoundA, dResultA, 0L);

        bool useA   = false;
        long offset = BATCH;

        while (!found && !cts.IsCancellationRequested)
        {
            var dFC = useA ? dFoundA  : dFoundB;
            var dRC = useA ? dResultA : dResultB;
            var dFP = useA ? dFoundB  : dFoundA;
            var dRP = useA ? dResultB : dResultA;
            int[]  hFP = useA ? hFB : hFA;
            long[] hRP = useA ? hRB : hRA;

            bool hasMore = offset < total && !found;
            int  size    = hasMore ? (int)Math.Min(BATCH, total - offset) : 0;

            if (hasMore)
            {
                dFC.MemSetToZero(); dRC.MemSetToZero();
                launch(size, dFC, dRC, offset);
            }

            accel.Synchronize();
            dFP.CopyToCPU(hFP);

            if (hFP[0] == 1)
            {
                dRP.CopyToCPU(hRP);
                lastGuess = decode(hRP[0]);
                Console.WriteLine($"\n\nPassword cracked: {lastGuess}");
                found = true; break;
            }

            long prevSize = offset == BATCH ? firstSize : Math.Min(BATCH, total - (offset - BATCH));
            Interlocked.Add(ref attempts, prevSize);
            lastGuess = $"batch @ {offset - BATCH:N0}";

            if (!hasMore) break;
            offset += BATCH;
            useA = !useA;
        }

        if (!found)
        {
            accel.Synchronize();
            var dFL = useA ? dFoundB  : dFoundA;
            var dRL = useA ? dResultB : dResultA;
            int[] hFL = new int[1]; long[] hRL = new long[1];
            dFL.CopyToCPU(hFL);
            if (hFL[0] == 1)
            {
                dRL.CopyToCPU(hRL);
                lastGuess = decode(hRL[0]);
                Console.WriteLine($"\n\nPassword cracked: {lastGuess}");
                found = true;
            }
        }

        sw.Stop(); found = true;
        Console.WriteLine($"\nTime: {sw.Elapsed.TotalSeconds:F2}s | Attempts: {attempts:N0}");
    }
}