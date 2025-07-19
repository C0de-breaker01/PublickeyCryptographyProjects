#include <stdio.h>
#include <string.h>
#include <openssl/bn.h>
#include <openssl/rand.h>
#define MAX_BITS 2048
#define MAX_STRING_LENGTH 8192  // 最大字符串长度
#define LOW_LEVEL_PRIMALITY_TEST_BITS 512  // 低位试除法素性检验
#define BLOCK_SIZE 128  // 每块字节数（确保m < q）
#define MILLER_RABIN_ITERATIONS 20  // Miller-Rabin测试迭代次数
#define HEX_OR_DECIMAL 1  // 十六进制(1)或十进制(0)格式
#define FILE_NAME "key_cipher.txt"
// 写入BIGNUM到文件
void write_bignum_to_file(const char *filename, char *num) {
    FILE *file = fopen(filename, "a");
    if (!file) {
        printf("-Error: Failed to open or create file %s\n", filename);
        return;
    }
    fprintf(file, "%s\n", num);
    fclose(file);
}
// 生成大数
BIGNUM* generate_large_number(int bits) {
    BIGNUM *num = BN_new();
    BN_rand(num, bits, 0, 0);  // 生成一个bits位的随机数
    return num;
}
// 低位试除法素性检验
int is_prime_low_level(BIGNUM *n) {
    BIGNUM *two = BN_new();
    BN_set_word(two, 2);
    // 基本检查
    if (BN_cmp(n, two) < 0) { BN_free(two); return 0; }  // 小于2的数不是素数
    if (BN_cmp(n, two) == 0) { BN_free(two); return 1; }  // 2是素数
    if (!BN_is_odd(n)) { BN_free(two); return 0; }  // 偶数不是素数（除了2）
    BN_free(two);
    // 初始化试除用的变量
    BIGNUM *i = BN_new();
    BIGNUM *i_squared = BN_new();
    BN_CTX *ctx = BN_CTX_new();
    int is_prime = 1;  // 假设是素数，直到找到反例
    BN_set_word(i, 3);
    BN_mul(i_squared, i, i, ctx);
    while (BN_cmp(i_squared, n) <= 0) {  // 当 i*i <= n 时继续循环
        if (BN_mod_word(n, BN_get_word(i)) == 0) {
            is_prime = 0;  // 找到因子，n不是素数
            break;
        }
        // 增加 i 并更新 i_squared
        BN_add_word(i, 2);  // i += 2
        BN_mul(i_squared, i, i, ctx);  // 更新 i_squared
    }
    // 清理资源
    BN_free(i);
    BN_free(i_squared);
    BN_CTX_free(ctx);
    return is_prime;
}
// Miller-Rabin素性测试
int is_prime(BIGNUM *n, int iterations) {
    BIGNUM *two = BN_new();
    BN_set_word(two, 2);
    if (BN_cmp(n, two) < 0) { BN_free(two); return 0; }
    if (BN_cmp(n, two) == 0) { BN_free(two); return 1; }
    if (!BN_is_odd(n)) { BN_free(two); return 0; }
    BN_CTX *ctx = BN_CTX_new();
    BIGNUM *a = BN_new();
    BIGNUM *d = BN_new();
    BIGNUM *n_minus_1 = BN_new();
    BIGNUM *x = BN_new();
    int result = 1;
    // n - 1
    BN_sub(n_minus_1, n, BN_value_one());
    // d = n - 1
    BN_copy(d, n_minus_1);
    // 将d分解为2^r * d'，其中d'是奇数
    int r = 0;
    while (!BN_is_odd(d)) {
        BN_rshift1(d, d);
        r++;
    }
    for (int i = 0; i < iterations; i++) {
        // 生成 [2, n-2] 范围的随机数
        do {
            BN_rand_range(a, n_minus_1);
        } while (BN_cmp(a, two) < 0);
        // x = a^d mod n
        BN_mod_exp(x, a, d, n, ctx);
        if (BN_is_one(x) || BN_cmp(x, n_minus_1) == 0) continue;
        int passed = 0;
        for (int j = 0; j < r - 1; j++) {
            // x = x^2 mod n
            BN_mod_sqr(x, x, n, ctx);
            if (BN_is_one(x)) {
                result = 0;
                goto cleanup;
            }
            if (BN_cmp(x, n_minus_1) == 0) {
                passed = 1;
                break;
            }
        }
        if (!passed) {
            result = 0;
            goto cleanup;
        }
    }
    cleanup:
        BN_free(a);
        BN_free(d);
        BN_free(n_minus_1);
        BN_free(x);
        BN_CTX_free(ctx);
        BN_free(two);
    return result;
}
// 生成大素数（安全素数）
BIGNUM* generate_prime(int bits) {
    BIGNUM *p = NULL;
    do {
        p = generate_large_number(bits);
    } while (!is_prime(p, MILLER_RABIN_ITERATIONS));  // 使用20次Miller-Rabin测试
    return p;
}
// 生成生成元g（模p的原根）
BIGNUM* find_generator(BIGNUM *p) {
    BN_CTX *ctx = BN_CTX_new();
    BIGNUM *g = BN_new();
    BIGNUM *q = BN_new();  // q = (p-1)/2，使用阶为q的生成元满足DDH条件
    BIGNUM *tmp = BN_new();
    // 计算q = (p-1)/2
    BN_sub(q, p, BN_value_one()); // q = p-1
    BN_rshift1(q, q);             // q = (p-1)/2
    // 随机选择g直到满足条件：g^q mod p != 1
    do {
        BN_rand_range(g, p);  // 0 <= g < p
        if (BN_is_zero(g)) continue;
        BN_mod_exp(tmp, g, q, p, ctx);
    } while (BN_is_one(tmp));
    BN_free(q);
    BN_free(tmp);
    BN_CTX_free(ctx);
    return g;
}
// 生成密钥对
void generate_key_pair(BIGNUM **p, BIGNUM **g, BIGNUM **x, BIGNUM **y) {
    *p = generate_prime(MAX_BITS);
    *g = find_generator(*p);
    BN_CTX *ctx = BN_CTX_new();
    *x = BN_new();  // 私钥
    *y = BN_new();  // 公钥
    // 随机选择私钥x（1 < x < p-1）
    BIGNUM *pm1 = BN_new();
    BN_sub(pm1, *p, BN_value_one());
    BN_rand_range(*x, pm1);
    if (BN_is_zero(*x)) BN_add_word(*x, 1);
    // 计算公钥y = g^x mod p
    BN_mod_exp(*y, *g, *x, *p, ctx);
    BN_free(pm1);
    BN_CTX_free(ctx);
}
// 加密单个块
void encrypt_block(BIGNUM *m, BIGNUM *p, BIGNUM *g, BIGNUM *y, BIGNUM **c1, BIGNUM **c2) {
    BN_CTX *ctx = BN_CTX_new();
    BIGNUM *k = BN_new();
    BIGNUM *s = BN_new();
    // 随机选择k（1 < k < p-1）
    BIGNUM *pm1 = BN_new();
    BN_sub(pm1, p, BN_value_one());
    BN_rand_range(k, pm1);
    if (BN_is_zero(k)) BN_add_word(k, 1);
    // 计算c1 = g^k mod p
    *c1 = BN_new();
    BN_mod_exp(*c1, g, k, p, ctx);
    // 计算s = y^k mod p
    BN_mod_exp(s, y, k, p, ctx);
    // 计算c2 = m * s mod p
    *c2 = BN_new();
    BN_mod_mul(*c2, m, s, p, ctx);
    BN_free(k);
    BN_free(s);
    BN_free(pm1);
    BN_CTX_free(ctx);
}
// 解密单个块
void decrypt_block(BIGNUM *c1, BIGNUM *c2, BIGNUM *p, BIGNUM *x, BIGNUM **m) {
    BN_CTX *ctx = BN_CTX_new();
    BIGNUM *s = BN_new();
    // 计算s = c1^x mod p
    BN_mod_exp(s, c1, x, p, ctx);
    // 计算s的逆
    BIGNUM *s_inv = BN_mod_inverse(NULL, s, p, ctx);
    if (s_inv == NULL) {
        printf("-Error: modular inverse does not exist.\n");
        BN_free(s);
        BN_CTX_free(ctx);
        *m = NULL;
        return;
    }
    // 计算m = c2 * s_inv mod p
    *m = BN_new();
    BN_mod_mul(*m, c2, s_inv, p, ctx);
    BN_free(s);
    BN_free(s_inv);
    BN_CTX_free(ctx);
}
// 加密调用函数
void encrypt_message(void) {
    // 获取用户输入
    // getchar();  // 清除输入缓冲区中的换行符
    printf("-Starting ElGamal Encryption...\n");
    char plaintext[MAX_STRING_LENGTH];
    printf("-Enter text to encrypt(less than %zu bytes): ", MAX_STRING_LENGTH);
    fgets(plaintext, sizeof(plaintext), stdin);
    plaintext[strcspn(plaintext, "\n")] = '\0';  // 移除换行符
    size_t text_len = strlen(plaintext);
    size_t num_blocks = (text_len + BLOCK_SIZE - 1) / BLOCK_SIZE;
    // 打印输入文本长度和块数
    printf("-Text length: %zu bytes\n", text_len);
    if (text_len > MAX_STRING_LENGTH) {
        printf("-Error: Text exceeds maximum length of %d bytes.\n", MAX_STRING_LENGTH);
        return;
    }
    printf("\n-Encrypting %zu blocks...\n", num_blocks);
    // 初始化OpenSSL随机数生成器
    RAND_poll();
    // 生成密钥对
    BIGNUM *p = NULL, *g = NULL, *x = NULL, *y = NULL;
    printf("-Generating keys (this may take a few seconds)...\n");
    generate_key_pair(&p, &g, &x, &y);
    if (HEX_OR_DECIMAL == 1) {
        printf("-Using hexadecimal format for keys.\n");
        // 打印公钥和私钥(hex格式)
        char *p_str = BN_bn2hex(p);
        char *g_str = BN_bn2hex(g);
        char *y_str = BN_bn2hex(y);
        char *x_str = BN_bn2hex(x);
        printf("\n-Public Key (p, g, y):\n");
        printf("-p = %s\n", p_str);
        printf("-g = %s\n", g_str);
        printf("-y = %s\n\n", y_str);
        printf("-Private Key (x):\n");
        printf("-x = %s\n\n", x_str);
        // 写入文件
        write_bignum_to_file(FILE_NAME, p_str);
        write_bignum_to_file(FILE_NAME, g_str);
        write_bignum_to_file(FILE_NAME, y_str);
        write_bignum_to_file(FILE_NAME, x_str);
        OPENSSL_free(p_str);
        OPENSSL_free(g_str);
        OPENSSL_free(y_str);
        OPENSSL_free(x_str);
    } else {
        printf("-Using decimal format for keys.\n");
        // 打印公钥和私钥(decimal格式)
        printf("\n-Public Key (p, g, y):\n");
        printf("-p = %s\n", BN_bn2dec(p));
        printf("-g = %s\n", BN_bn2dec(g));
        printf("-y = %s\n\n", BN_bn2dec(y));
        printf("-Private Key (x):\n");
        printf("-x = %s\n\n", BN_bn2dec(x));
        // 写入文件
        write_bignum_to_file(FILE_NAME, BN_bn2dec(p));
        write_bignum_to_file(FILE_NAME, BN_bn2dec(g));
        write_bignum_to_file(FILE_NAME, BN_bn2dec(y));
        write_bignum_to_file(FILE_NAME, BN_bn2dec(x));
    }
    // 加密每个块
    BIGNUM **c1_list = malloc(num_blocks * sizeof(BIGNUM*));
    BIGNUM **c2_list = malloc(num_blocks * sizeof(BIGNUM*));
    for (size_t i = 0; i < num_blocks; i++) {
        // 准备当前块
        size_t block_len = (i == num_blocks - 1) ? text_len - i * BLOCK_SIZE : BLOCK_SIZE;
        unsigned char block[BLOCK_SIZE] = {0};
        memcpy(block, plaintext + i * BLOCK_SIZE, block_len);
        // 转换为BIGNUM
        BIGNUM *m = BN_bin2bn(block, BLOCK_SIZE, NULL);
        // 加密
        encrypt_block(m, p, g, y, &c1_list[i], &c2_list[i]);
        BN_free(m);
    }
    // 打印密文摘要
    printf("\n-Ciphertext:\n");
    if (HEX_OR_DECIMAL == 1) {
        printf("-Using hexadecimal format for ciphertext.\n");
        for (size_t i = 0; i < num_blocks; i++) {
            char *c1_hex = BN_bn2hex(c1_list[i]);
            char *c2_hex = BN_bn2hex(c2_list[i]);
            printf("-Block %zu:\n c1 = %s\n c2 = %s\n", i, c1_hex, c2_hex);
            // 写入文件
            write_bignum_to_file(FILE_NAME, c1_hex);
            write_bignum_to_file(FILE_NAME, c2_hex);
            OPENSSL_free(c1_hex);
            OPENSSL_free(c2_hex);
        }
    } else {
        printf("-Using decimal format for ciphertext.\n");
        for (size_t i = 0; i < num_blocks; i++) {
            char *c1_dec = BN_bn2dec(c1_list[i]);
            char *c2_dec = BN_bn2dec(c2_list[i]);
            printf("-Block %zu:\n c1 = %s\n c2 = %s\n", i, c1_dec, c2_dec);
            // 写入文件
            write_bignum_to_file(FILE_NAME, c1_dec);
            write_bignum_to_file(FILE_NAME, c2_dec);
            OPENSSL_free(c1_dec);
            OPENSSL_free(c2_dec);
        }
    }
    // 清理内存
    BN_free(p);
    BN_free(g);
    BN_free(x);
    BN_free(y);
    for (size_t i = 0; i < num_blocks; i++) {
        BN_free(c1_list[i]);
        BN_free(c2_list[i]);
    }
    free(c1_list);
    free(c2_list);
}
// 解密调用函数
void decrypt_message(void) {
    // 询问是否解密
    getchar();
    printf("-Decrypt? (y/n): ");
    char response[10];
    fgets(response, sizeof(response), stdin);
    if (response[0] == 'y' || response[0] == 'Y') {
        printf("-Enter the number of blocks to decrypt:\n");
        size_t text_len, num_blocks;
        text_len = MAX_STRING_LENGTH;
        scanf("%zu", &num_blocks);
        getchar();  // 清除输入缓冲区中的换行符
        // 检查块数是否有效
        if (num_blocks == 0 || num_blocks > MAX_STRING_LENGTH / BLOCK_SIZE) {
            printf("-Invalid number of blocks. Please try again.\n");
            return;
        }
        BIGNUM *p_dec = NULL, *g_dec = NULL, *y_dec = NULL, *x_dec = NULL;
        char p_input[MAX_STRING_LENGTH], g_input[MAX_STRING_LENGTH], y_input[MAX_STRING_LENGTH], x_input[MAX_STRING_LENGTH];
        if (HEX_OR_DECIMAL == 1) {
            printf("-Using hexadecimal format for decryption.\n");
            printf("-enter publickey p(hex), g(hex), y(hex) and privatekey x(hex)to decrypt:\n");
            printf("-enter publickey p(hex):");
            fgets(p_input, sizeof(p_input), stdin);
            printf("-enter publickey g(hex):");
            fgets(g_input, sizeof(g_input), stdin);
            printf("-enter publickey y(hex):");
            fgets(y_input, sizeof(y_input), stdin);
            printf("-enter privatekey x(hex):");
            fgets(x_input, sizeof(x_input), stdin);
            // 移除输入中的换行符
            p_input[strcspn(p_input, "\n")] = '\0';
            g_input[strcspn(g_input, "\n")] = '\0';
            y_input[strcspn(y_input, "\n")] = '\0';
            x_input[strcspn(x_input, "\n")] = '\0';
            // 检查输入是否为十六进制
            for (size_t i = 0; i < strlen(p_input); i++) {
                if (!((p_input[i] >= '0' && p_input[i] <= '9') || (p_input[i] >= 'a' && p_input[i] <= 'f') || (p_input[i] >= 'A' && p_input[i] <= 'F'))) {
                    printf("-Invalid hexadecimal input. Please enter valid hexadecimal values.\n");
                    return;
                }
            }
            // 转换为BIGNUM
            BN_hex2bn(&p_dec, p_input);
            BN_hex2bn(&g_dec, g_input);
            BN_hex2bn(&y_dec, y_input);
            BN_hex2bn(&x_dec, x_input);
        } else {
            printf("-Using decimal format for decryption.\n");
            printf("-enter publickey p(dec), g(dec), y(dec) and privatekey x(dec)to decrypt:\n");
            printf("-enter publickey p(dec):");
            fgets(p_input, sizeof(p_input), stdin);
            printf("-enter publickey g(dec):");
            fgets(g_input, sizeof(g_input), stdin);
            printf("-enter publickey y(dec):");
            fgets(y_input, sizeof(y_input), stdin);
            printf("-enter privatekey x(dec):");
            fgets(x_input, sizeof(x_input), stdin);
            // 移除输入中的换行符
            p_input[strcspn(p_input, "\n")] = '\0';
            g_input[strcspn(g_input, "\n")] = '\0';
            y_input[strcspn(y_input, "\n")] = '\0';
            x_input[strcspn(x_input, "\n")] = '\0';
            // 检查输入是否为十进制
            for (size_t i = 0; i < strlen(p_input); i++) {
                if (!(p_input[i] >= '0' && p_input[i] <= '9')) {
                    printf("-Invalid decimal input. Please enter valid decimal values.\n");
                    return;
                }
            }
            // 转换为BIGNUM (十进制)
            BN_dec2bn(&p_dec, p_input);
            BN_dec2bn(&g_dec, g_input);
            BN_dec2bn(&y_dec, y_input);
            BN_dec2bn(&x_dec, x_input);
        }
        unsigned char decrypted_block[BLOCK_SIZE];
        char *full_decrypt = calloc(1, text_len + 1);
        if (full_decrypt == NULL) {
            printf("-Error: Memory allocation failed.\n");
            BN_free(p_dec);
            BN_free(g_dec);
            BN_free(y_dec);
            BN_free(x_dec);
            return;
        }
        for (size_t i = 0; i < num_blocks; i++) {
            char c1_input[MAX_STRING_LENGTH], c2_input[MAX_STRING_LENGTH];
            // 根据HEX_OR_DECIMAL设置提示正确的输入格式
            if (HEX_OR_DECIMAL == 1) {
                printf("-Enter c1 for block %zu (hex): ", i);
            } else {
                printf("-Enter c1 for block %zu (dec): ", i);
            }
            fgets(c1_input, sizeof(c1_input), stdin);
            c1_input[strcspn(c1_input, "\n")] = '\0';
            if (HEX_OR_DECIMAL == 1) {
                printf("-Enter c2 for block %zu (hex): ", i);
            } else {
                printf("-Enter c2 for block %zu (dec): ", i);
            }
            fgets(c2_input, sizeof(c2_input), stdin);
            c2_input[strcspn(c2_input, "\n")] = '\0';
            BIGNUM *c1_bn = NULL, *c2_bn = NULL;
            // 根据当前模式转换输入
            if (HEX_OR_DECIMAL == 1) {
                // 检查输入是否为有效的十六进制
                for (size_t i = 0; i < strlen(c1_input); i++) {
                    if (!((c1_input[i] >= '0' && c1_input[i] <= '9') || (c1_input[i] >= 'a' && c1_input[i] <= 'f') || (c1_input[i] >= 'A' && c1_input[i] <= 'F'))) {
                        printf("-Invalid hexadecimal input. Please enter valid hexadecimal values.\n");
                        return;
                    }
                }
                for (size_t i = 0; i < strlen(c2_input); i++) {
                    if (!((c2_input[i] >= '0' && c2_input[i] <= '9') || (c2_input[i] >= 'a' && c2_input[i] <= 'f') || (c2_input[i] >= 'A' && c2_input[i] <= 'F'))) {
                        printf("-Invalid hexadecimal input. Please enter valid hexadecimal values.\n");
                        return;
                    }
                }
                BN_hex2bn(&c1_bn, c1_input);
                BN_hex2bn(&c2_bn, c2_input);
            } else {
                // 检查输入是否为有效的十进制
                for (size_t i = 0; i < strlen(c1_input); i++) {
                    if (!(c1_input[i] >= '0' && c1_input[i] <= '9')) {
                        printf("-Invalid decimal input. Please enter valid decimal values.\n");
                        return;
                    }
                }
                for (size_t i = 0; i < strlen(c2_input); i++) {
                    if (!(c2_input[i] >= '0' && c2_input[i] <= '9')) {
                        printf("-Invalid decimal input. Please enter valid decimal values.\n");
                        return;
                    }
                }
                BN_dec2bn(&c1_bn, c1_input);
                BN_dec2bn(&c2_bn, c2_input);
            }
            if (c1_bn == NULL || c2_bn == NULL) {
                printf("-Error converting input to BIGNUM. Skipping block %zu.\n", i);
                if (c1_bn) BN_free(c1_bn);
                if (c2_bn) BN_free(c2_bn);
                continue;
            }
            BIGNUM *m_dec = NULL;
            printf("\n-Decrypting block %zu...\n", i);
            decrypt_block(c1_bn, c2_bn, p_dec, x_dec, &m_dec);
            if (m_dec == NULL) {
                printf("-Error: Decryption failed for block %zu.\n", i);
                BN_free(c1_bn);
                BN_free(c2_bn);
                continue;
            }
            // 将BIGNUM转回字节
            int len = BN_bn2bin(m_dec, decrypted_block);
            size_t block_len = (i == num_blocks - 1) ? text_len - i * BLOCK_SIZE : BLOCK_SIZE;
            // 确保不越界
            size_t copy_len = (len < (int)block_len) ? len : block_len;
            memcpy(full_decrypt + i * BLOCK_SIZE, decrypted_block, copy_len);
            BN_free(m_dec);
            BN_free(c1_bn);
            BN_free(c2_bn);
        }
        printf("-Decrypted text: %s\n", full_decrypt);
        free(full_decrypt);
        BN_free(p_dec);
        BN_free(g_dec);
        BN_free(y_dec);
        BN_free(x_dec);
    }
    else {
        printf("-Decryption skipped.\n");
    }
}
// 素性检验调用函数
void primality_test(void) {
    //getchar();
    printf("-Enter a number(dec) to test for primality.\n");
    BIGNUM *n = BN_new();
    char input[MAX_STRING_LENGTH];
    scanf("%s", input);
    // 检查输入长度
    if (strlen(input) > MAX_STRING_LENGTH - 1 || strlen(input) == 0) {
        printf("-Something went wrong!T^T. Please enter a valid number.\n");
        BN_free(n);
        return;
    }
    // 将输入转换为BIGNUM
    if (BN_dec2bn(&n, input) == 0) {
        printf("-Invalid number format. Please enter a valid decimal number.\n");
        BN_free(n);
        return;
    }
    if (BN_is_negative(n) || BN_is_zero(n)) {
        printf("-Something went wrong!T^T. Please enter a valid number.\n");
        BN_free(n);
        return;
    }
    int is_prime_result;
    if (strlen(input) < LOW_LEVEL_PRIMALITY_TEST_BITS / 4) {
        printf("-Using low-level primality test for small numbers...\n");
        is_prime_result = is_prime_low_level(n);
        if (is_prime_result) {
            printf("The number %s is prime.\n", input);
        } else {
            printf("The number %s is not prime.\n", input);
        }
        BN_free(n);
        return;
    } else {
        printf("-Using Miller-Rabin primality test for large numbers...\n");
        is_prime_result = is_prime(n, 20);  // 使用20次Miller-Rabin测试
        if (is_prime_result) {
            printf("The number %s is probably prime.\n", input);
        } else {
            printf("The number %s is not prime.\n", input);
        }
        BN_free(n);
        return;
    }
}
// 菜单
int menu(void) {
    printf("1. Primality Test\n");
    printf("2. Encrypt Message\n");
    printf("3. Decrypt Message\n");
    printf("4. Clear the text in %s\n", FILE_NAME);
    printf("5. Exit\n");
    printf("-Please select an option: ");
    int choice;
    if (scanf("%d", &choice) != 1 || choice < 1 || choice > 5) {
        printf("-Invalid input. Please enter a valid number.\n");
        while (getchar() != '\n');  // 清空输入缓冲区
        return menu();  // 递归调用以重新显示菜单
    }
    return choice;
}
// int main(void) {
//     printf("=================Welcome to the Primality Test and ElGamal Encryption Program!=================\n");
//     int choice;
//     choice = menu();
//     while (choice != 5) {
//         switch (choice) {
//             case 1:
//                 primality_test();
//                 break;
//             case 2:
//                 encrypt_message();
//                 break;
//             case 3:
//                 decrypt_message();
//                 break;
//             case 4:
//                 // 清空文件内的文本
//                 {
//                     FILE *file = fopen(FILE_NAME, "w");
//                     if (file) {
//                         fclose(file);
//                         printf("-The text in %s has been cleared.\n", FILE_NAME);
//                     } else {
//                         printf("-Error: Could not clear the file %s.\n", FILE_NAME);
//                     }
//                 }
//                 break;
//             case 5:
//                 printf("-Exiting the program. Goodbye!\n");
//                 return 0;
//             default:
//                 printf("-Invalid choice. Please try again.\n");
//         }
//         choice = menu();
//     }
//     return 0;
// }