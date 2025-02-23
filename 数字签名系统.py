import tkinter as tk                      # 导入 tkinter，用于创建图形界面
from tkinter import scrolledtext, filedialog, ttk, font, messagebox
from PIL import Image, ImageTk            # 导入 Pillow 库，用于图像处理
from Crypto.Hash import SHA256            # 导入 PyCryptoDome 的 SHA256 哈希类
from gmssl import sm2, func               # 导入 gmssl 库中的 sm2 和 func，用于 SM2 算法
import base64                             # 导入 base64，用于编解码
import os                                 # 导入 os，用于文件和路径操作
import random                             # 导入 random，用于生成随机数
from gmpy2 import invert                  # 从 gmpy2 导入 invert，用于大数求逆
import sys                                # 导入 sys，用于读取系统路径、打包资源等
import json                               # 导入 json，用于读写 JSON 文件
from packaging import version             # 导入 packaging 库，用于比较版本号
import PIL                                # 导入 PIL 包，用于检查其版本

def resource_path(relative_path):
    """获取资源的绝对路径"""
    try:
        # PyInstaller 创建临时文件夹, 将路径存储在 _MEIPASS 中
        base_path = sys._MEIPASS
    except Exception:
        # 如果不是打包环境，则使用当前目录
        base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)

# 检查 Pillow 版本
if version.parse(PIL.__version__) < version.parse("10.0.0"):
    # 在 GUI 中弹出警告窗口
    root_warning = tk.Tk()
    root_warning.withdraw()  # 隐藏主窗口
    messagebox.showwarning("警告", "Pillow 版本过低，建议更新到10.0.0或更高版本以确保兼容性。")
    root_warning.destroy()

# SM2 椭圆曲线公共参数（中国国密标准曲线）
p = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF  # 模数 p
a = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFC  # 曲线参数 a
b = 0x28E9FA9E9D9F5E344D5A9E4BCF6509A7F39789F515AB8F92DDBCBD414D940E93  # 曲线参数 b
n = 0xFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFF7203DF6B21C6052B53BBF40939D54123  # 生成元阶 n
Gx = 0x32C4AE2C1F1981195F9904466A39C9948FE30BBFF2660BE1715A4589334C74C7  # 生成元 G 的 x 坐标
Gy = 0xBC3736A2F4F6779C59BDCEE36B692153D0A9877CC62A474002DF32E52139F0A0  # 生成元 G 的 y 坐标

def point_add(P1x, P1y, P2x, P2y):
    """椭圆曲线点加运算"""
    if P1x == 0 and P1y == 0:
        return P2x, P2y
    if P2x == 0 and P2y == 0:
        return P1x, P1y

    # 若点坐标相同但 y 坐标相反，则返回无穷远点(0,0)
    if P1x == P2x and P1y != P2y:
        return 0, 0

    # 计算 λ (斜率)
    if P1x != P2x:
        lam = ((P2y - P1y) * invert(P2x - P1x, p)) % p
    else:
        # 当 P1x == P2x 时，需要使用双倍公式
        lam = ((3 * P1x * P1x + a) * invert(2 * P1y, p)) % p

    # 计算结果点的坐标
    x3 = (lam * lam - P1x - P2x) % p
    y3 = (lam * (P1x - x3) - P1y) % p
    return x3, y3

def point_mul(k, Px, Py):
    """椭圆曲线标量乘运算（k * P）"""
    Qx, Qy = 0, 0              # 初始化为无穷远点
    k_bin = bin(k)[2:]         # 将 k 转化为二进制字符串

    for i in k_bin:
        # 先做一次自加（Q = Q + Q）
        Qx, Qy = point_add(Qx, Qy, Qx, Qy)
        # 如果当前二进制位是 '1'，则再加上基点 P
        if i == '1':
            Qx, Qy = point_add(Qx, Qy, Px, Py)

    return Qx, Qy

def generate_key():
    """生成 SM2 公私钥对"""
    private_key = random.randint(1, n-1)         # 随机生成私钥
    public_key = point_mul(private_key, Gx, Gy)  # 利用私钥生成公钥
    return private_key, public_key

def sm2_sign(message_hash, private_key, k=None):
    """
    使用 SM2 对消息哈希进行签名
    message_hash: 16进制形式的哈希字符串
    private_key: 私钥(int类型)
    k: 可选的随机数，若不传则自动生成
    """
    if k is None:
        k = random.randint(1, n-1)  # 随机选取 k

    x1, y1 = point_mul(k, Gx, Gy)                     # 计算 k*G
    r = (int(message_hash, 16) + x1) % n              # 计算 r
    if r == 0 or r + k == n:
        # 若出现 r = 0 或 r+k = n，则重新签名
        return sm2_sign(message_hash, private_key)

    # 计算 s = ( (k - r*private_key) * (1 + private_key)^-1 ) mod n
    s = (invert(1 + private_key, n) * (k - r * private_key)) % n
    if s == 0:
        # 若 s = 0 则重新签名
        return sm2_sign(message_hash, private_key)

    # 返回 r 与 s 的 16 进制形式（填充至 64 个字符）
    return (hex(r)[2:].zfill(64), hex(s)[2:].zfill(64))

def sm2_verify(message_hash, signature, public_key):
    """
    使用 SM2 公钥验证签名
    message_hash: 16进制形式的哈希字符串
    signature: (r, s) 元组
    public_key: (Px, Py) 元组
    """
    r, s = int(signature[0], 16), int(signature[1], 16)
    # 检查 r、s 范围
    if r < 1 or r > n-1 or s < 1 or s > n-1:
        return False

    t = (r + s) % n
    if t == 0:
        return False

    # 计算 s*G 与 t*Q
    x1, y1 = point_mul(s, Gx, Gy)
    x2, y2 = point_mul(t, public_key[0], public_key[1])

    # 点加
    x, y = point_add(x1, y1, x2, y2)

    # 计算 R
    R = (int(message_hash, 16) + x) % n
    return R == r

def resize_image(image, size):
    """封装图像重采样函数，根据 Pillow 版本兼容使用"""
    try:
        # Pillow 10.0.0 之后使用 Resampling.LANCZOS
        return image.resize(size, Image.Resampling.LANCZOS)
    except AttributeError:
        # 旧版本 Pillow 使用 Image.ANTIALIAS
        return image.resize(size, Image.ANTIALIAS)

# 全局变量
private_key = None                  # 签名系统的私钥
public_key = None                   # 签名系统的公钥
signing_signature = None            # 存放签名系统的数字签名
hash_value = None                   # 存放哈希值

# 验证系统全局变量
verification_signature = None       # 验证系统的数字签名
verification_ciphertext = None      # 验证系统的密文
uploaded_certificate = None         # 用户上传的证书

# CA 全局变量
ca_private_key = None              # CA 私钥
ca_public_key = None               # CA 公钥
issued_certificates = []           # 已颁发的数字证书列表
user_public_key_for_certificate = None  # 用于给用户颁发证书时，保存用户公钥
username_for_certificate = ""            # 用于给用户颁发证书时，保存用户名

def load_certificate_repository():
    """
    加载或初始化证书存储库（JSON 文件），并将其读取到 issued_certificates 中
    """
    global issued_certificates
    repo_path = "cert_repository.json"
    if os.path.exists(repo_path):
        with open(repo_path, 'r', encoding='utf-8') as repo_file:
            try:
                issued_certificates = json.load(repo_file)
                # 读取到的必须是列表结构，否则重新初始化
                if not isinstance(issued_certificates, list):
                    raise ValueError("证书存储库格式错误，应为列表")
            except (json.decoder.JSONDecodeError, ValueError) as e:
                print(f"加载证书存储库失败: {e}")
                issued_certificates = []
                # 重新写回空列表到文件
                with open(repo_path, 'w', encoding='utf-8') as f:
                    json.dump(issued_certificates, f, ensure_ascii=False, indent=4)
    else:
        issued_certificates = []
        with open(repo_path, 'w', encoding='utf-8') as repo_file:
            json.dump(issued_certificates, repo_file, ensure_ascii=False, indent=4)

def save_certificate_repository():
    """将 issued_certificates 列表写入到 cert_repository.json"""
    repo_path = "cert_repository.json"
    with open(repo_path, 'w', encoding='utf-8') as repo_file:
        json.dump(issued_certificates, repo_file, ensure_ascii=False, indent=4)

def generate_keys_with_id_signing(user_id):
    """
    使用用户 ID 生成密钥对（示例中并未真正用 ID 作为随机种子），
    并在文本框中显示公私钥
    """
    global private_key, public_key, sm2_crypt
    try:
        # 如果用户未输入 ID，则抛出异常
        if not user_id:
            raise ValueError("请输入用户ID")

        # 生成密钥对
        private_key, public_key = generate_key()

        # 将公钥拼接为 04 + x + y 的十六进制
        public_key_hex = f"04{hex(public_key[0])[2:].zfill(64)}{hex(public_key[1])[2:].zfill(64)}"
        # 初始化 SM2 加密对象
        sm2_crypt = sm2.CryptSM2(public_key=public_key_hex, private_key=hex(private_key)[2:].zfill(64))

        # 显示在文本框中
        public_key_box.delete('1.0', tk.END)
        private_key_box.delete('1.0', tk.END)
        public_key_box.insert(tk.END, public_key_hex)
        private_key_box.insert(tk.END, hex(private_key)[2:].zfill(64))

        print(f"用户 {user_id} 的密钥生成成功")
        messagebox.showinfo("成功", f"用户 {user_id} 的密钥生成成功")
    except Exception as e:
        print(f"密钥生成失败: {e}")
        messagebox.showerror("错误", f"密钥生成失败: {e}")

def save_user_keys():
    """将当前生成或加载的用户公私钥保存到文件"""
    try:
        if not private_key or not public_key:
            raise ValueError("请先生成用户密钥")

        # 从输入框获取 user_id
        user_id = user_id_entry.get().strip()
        if not user_id:
            raise ValueError("请先输入用户ID")

        # 弹出选择保存目录对话框
        save_dir = filedialog.askdirectory(title="选择密钥保存目录")
        if not save_dir:
            return

        if not os.path.exists(save_dir):
            os.makedirs(save_dir)

        # 保存公钥为 txt 文件
        public_key_hex = f"04{hex(public_key[0])[2:].zfill(64)}{hex(public_key[1])[2:].zfill(64)}"
        public_key_filename = f"{user_id}_public_key.txt"
        with open(os.path.join(save_dir, public_key_filename), 'w') as pub_file:
            pub_file.write(public_key_hex)

        # 保存私钥
        private_key_filename = f"{user_id}_private_key.txt"
        with open(os.path.join(save_dir, private_key_filename), 'w') as priv_file:
            priv_file.write(hex(private_key)[2:].zfill(64))

        messagebox.showinfo("成功", "用户公私钥已保存")
        print("用户公私钥已保存")
    except Exception as e:
        print(f"密钥保存失败: {e}")
        messagebox.showerror("错误", f"密钥保存失败: {e}")

def load_user_keys_signing():
    """
    从文件中加载用户私钥及对应的公钥（签名系统），
    并初始化 sm2_crypt 对象
    """
    global private_key, public_key, sm2_crypt
    try:
        # 选择私钥文件
        priv_key_path = filedialog.askopenfilename(title="选择用户私钥文件", filetypes=[("Text files", "*.txt")])
        if not priv_key_path:
            return
        # 读取私钥
        with open(priv_key_path, 'r') as priv_file:
            private_key_hex = priv_file.read().strip()
            if len(private_key_hex) != 64:
                raise ValueError("私钥格式错误")
            private_key = int(private_key_hex, 16)
            private_key_box.delete('1.0', tk.END)
            private_key_box.insert(tk.END, private_key_hex)

        # 自动匹配公钥文件
        user_id = os.path.basename(priv_key_path).split('_private_key.txt')[0]
        pub_key_filename = f"{user_id}_public_key.txt"
        pub_key_path = os.path.join(os.path.dirname(priv_key_path), pub_key_filename)
        if not os.path.exists(pub_key_path):
            raise ValueError(f"对应的公钥文件 {pub_key_filename} 不存在")

        with open(pub_key_path, 'r') as pub_file:
            public_key_hex = pub_file.read().strip()
            if not public_key_hex.startswith('04') or len(public_key_hex) != 130:
                raise ValueError("公钥格式错误")
            public_key_box.delete('1.0', tk.END)
            public_key_box.insert(tk.END, public_key_hex)

        # 初始化 SM2 加密对象
        sm2_crypt = sm2.CryptSM2(public_key=public_key_hex, private_key=private_key_hex)

        messagebox.showinfo("成功", "用户密钥加载成功")
        print("用户密钥加载成功")
    except Exception as e:
        print(f"密钥加载失败: {e}")
        messagebox.showerror("错误", f"密钥加载失败: {e}")

def load_user_keys_verification():
    """
    从文件中加载用户私钥及对应的公钥（验证系统），
    并将私钥显示在 private_key_box_verify 中
    """
    global private_key, public_key, sm2_crypt
    try:
        # 选择私钥文件
        priv_key_path = filedialog.askopenfilename(title="选择用户私钥文件", filetypes=[("Text files", "*.txt")])
        if not priv_key_path:
            return
        # 读取私钥
        with open(priv_key_path, 'r') as priv_file:
            private_key_hex = priv_file.read().strip()
            if len(private_key_hex) != 64:
                raise ValueError("私钥格式错误")
            private_key = int(private_key_hex, 16)
            private_key_box_verify.delete('1.0', tk.END)
            private_key_box_verify.insert(tk.END, private_key_hex)

        # 自动匹配公钥文件
        user_id = os.path.basename(priv_key_path).split('_private_key.txt')[0]
        pub_key_filename = f"{user_id}_public_key.txt"
        pub_key_path = os.path.join(os.path.dirname(priv_key_path), pub_key_filename)
        if not os.path.exists(pub_key_path):
            raise ValueError(f"对应的公钥文件 {pub_key_filename} 不存在")

        with open(pub_key_path, 'r') as pub_file:
            public_key_hex = pub_file.read().strip()
            if not public_key_hex.startswith('04') or len(public_key_hex) != 130:
                raise ValueError("公钥格式错误")
            public_key_box.delete('1.0', tk.END)
            public_key_box.insert(tk.END, public_key_hex)

        # 初始化 SM2 加密对象
        sm2_crypt = sm2.CryptSM2(public_key=public_key_hex, private_key=private_key_hex)

        messagebox.showinfo("成功", "用户密钥加载成功")
        print("用户密钥加载成功")
    except Exception as e:
        print(f"密钥加载失败: {e}")
        messagebox.showerror("错误", f"密钥加载失败: {e}")

def upload_signer_public_key():
    """
    上传对方（签名者）的公钥文件并显示在 signer_public_key_box，
    用于验证系统
    """
    try:
        file_path = filedialog.askopenfilename(title="选择对方公钥文件", filetypes=[("Text files", "*.txt")])
        if not file_path:
            return
        with open(file_path, 'r') as pub_file:
            signer_public_key_hex = pub_file.read().strip()
            if not signer_public_key_hex.startswith('04') or len(signer_public_key_hex) != 130:
                raise ValueError("对方公钥格式错误")
            signer_public_key_box.delete('1.0', tk.END)
            signer_public_key_box.insert(tk.END, signer_public_key_hex)
            messagebox.showinfo("成功", "对方公钥上传成功")
            print("对方公钥上传成功")
    except Exception as e:
        print(f"对方公钥上传失败: {e}")
        messagebox.showerror("错误", f"对方公钥上传失败: {e}")

def load_plain_text_from_file():
    """从文本文件中读取明文并显示到 plain_text_box"""
    file_path = filedialog.askopenfilename(filetypes=[("Text files", "*.txt")])
    if file_path:
        with open(file_path, 'r', encoding='utf-8') as file:
            file_content = file.read()
            plain_text_box.delete('1.0', tk.END)
            plain_text_box.insert(tk.END, file_content)

def sha_hash():
    """对加密后的密文（Base64）进行 SHA256 哈希，并显示哈希结果"""
    global hash_value
    try:
        # 从 sm2_encrypt_box 获取密文（Base64）
        ciphertext_base64 = sm2_encrypt_box.get('1.0', tk.END).strip()
        if not ciphertext_base64:
            raise ValueError("密文未生成")
        
        # Base64 解码
        try:
            ciphertext = base64.b64decode(ciphertext_base64)
        except:
            raise ValueError("密文Base64格式错误")
        
        # 计算密文的 SHA256 哈希
        hash_obj = SHA256.new(ciphertext)
        hash_hex = hash_obj.hexdigest()
        hash_value = hash_hex

        # 显示哈希值
        sha_result_box.config(state='normal')
        sha_result_box.delete('1.0', tk.END)
        sha_result_box.insert(tk.END, hash_hex)
        sha_result_box.config(state='disabled')
        print("哈希计算成功")
    except Exception as e:
        print(f"哈希计算失败: {e}")
        messagebox.showerror("错误", f"哈希计算失败: {e}")

def sm2_sign_h1():
    """使用 SM2 对当前的 hash_value 进行签名，并显示结果"""
    global signing_signature
    if not private_key:
        print("请先生成密钥")
        messagebox.showwarning("警告", "请先生成密钥")
        return
    try:
        if not hash_value:
            raise ValueError("请先计算哈希值")
        
        # 进行签名
        r, s = sm2_sign(hash_value, private_key)
        signing_signature = f"{r}{s}"

        sm2_result_box.delete('1.0', tk.END)
        sm2_result_box.insert(tk.END, signing_signature)
        print("签名生成成功")
        messagebox.showinfo("成功", "签名生成成功")
    except Exception as e:
        print(f"签名生成失败: {e}")
        sm2_result_box.delete('1.0', tk.END)
        sm2_result_box.insert(tk.END, f"签名失败: {str(e)}")
        messagebox.showerror("错误", f"签名生成失败: {e}")

def sm2_encrypt():
    """使用 SM2 公钥加密 plain_text_box 中的明文，并显示加密结果（Base64）"""
    try:
        # 获取明文
        plain_text = plain_text_box.get('1.0', tk.END).strip().encode()
        if not plain_text:
            raise ValueError("明文未输入")

        # 获取接收者公钥
        recipient_public_key = recipient_public_key_box.get('1.0', tk.END).strip()
        if not recipient_public_key:
            raise ValueError("接收者公钥未输入")
        if not recipient_public_key.startswith('04') or len(recipient_public_key) != 130:
            raise ValueError("接收者公钥格式错误")

        # 初始化接收者的 SM2 加密对象（只需要公钥）
        recipient_sm2 = sm2.CryptSM2(public_key=recipient_public_key, private_key='')

        # 加密并进行 Base64 编码
        ciphertext = recipient_sm2.encrypt(plain_text)
        ciphertext_base64 = base64.b64encode(ciphertext).decode('utf-8')

        # 显示加密结果
        sm2_encrypt_box.delete('1.0', tk.END)
        sm2_encrypt_box.insert(tk.END, ciphertext_base64)
        print("加密成功")
        messagebox.showinfo("成功", "加密成功")
    except Exception as e:
        print(f"加密失败: {e}")
        messagebox.showerror("错误", f"加密失败: {e}")

def sm2_decrypt():
    """使用自己的私钥解密 sm2_decrypt_box 中的密文（Base64），并显示解密后的明文和哈希"""
    try:
        # 获取密文（Base64）
        ciphertext_base64 = sm2_decrypt_box.get('1.0', tk.END).strip()
        if not ciphertext_base64:
            raise ValueError("密文未输入")

        # Base64 解码
        try:
            ciphertext = base64.b64decode(ciphertext_base64)
        except:
            raise ValueError("密文Base64格式错误")

        # 检查是否已经初始化过 sm2_crypt（含私钥）
        if not sm2_crypt:
            raise ValueError("请先生成并加载用户密钥")

        # 解密
        decrypted_data = sm2_crypt.decrypt(ciphertext)
        if decrypted_data is None:
            raise ValueError("解密失败，可能密文不正确或私钥错误")

        # 显示解密结果（UTF-8 解码）
        decrypted_text = decrypted_data.decode('utf-8', errors='ignore')
        sm2_decrypt_box_result.delete('1.0', tk.END)
        sm2_decrypt_box_result.insert(tk.END, decrypted_text)
        print("解密成功")
        messagebox.showinfo("成功", "解密成功")

        # 计算解密后明文的 SHA256
        decrypted_hash = SHA256.new(decrypted_data).hexdigest()
        hash_display_box.config(state='normal')
        hash_display_box.delete('1.0', tk.END)
        hash_display_box.insert(tk.END, decrypted_hash)
        hash_display_box.config(state='disabled')
        print("解密后的哈希值已计算并显示")
    except Exception as e:
        print(f"解密失败: {e}")
        sm2_decrypt_box_result.delete('1.0', tk.END)
        sm2_decrypt_box_result.insert(tk.END, f"解密失败: {str(e)}")
        messagebox.showerror("错误", f"解密失败: {e}")

def sm2_verify_signature():
    """验证对方公钥签名的正确性，以及密文和签名是否匹配"""
    try:
        # 若既没有上传证书，也没有手动上传对方公钥，则报错
        if not uploaded_certificate and not signer_public_key_box.get('1.0', tk.END).strip():
            raise ValueError("请先上传证书或对方公钥后再进行验证")
        
        # 1. 获取签名
        signature_str = verification_signature_box.get('1.0', tk.END).strip()
        if not signature_str:
            raise ValueError("签名未上传")
        if len(signature_str) != 128:
            raise ValueError("签名长度错误，应为128字符（64字符r + 64字符s）")
        r = signature_str[:64]
        s = signature_str[64:]

        # 2. 获取密文（Base64）
        ciphertext_base64 = sm2_decrypt_box.get('1.0', tk.END).strip()
        if not ciphertext_base64:
            raise ValueError("密文未输入")

        # Base64 解码
        try:
            ciphertext = base64.b64decode(ciphertext_base64)
        except:
            raise ValueError("密文Base64格式错误")

        # 3. 计算密文的哈希值
        hash_obj = SHA256.new(ciphertext)
        hash_hex = hash_obj.hexdigest()

        # 4. 获取对方公钥
        signer_public_key = signer_public_key_box.get('1.0', tk.END).strip()
        if not signer_public_key:
            raise ValueError("对方公钥未提取，请确保已上传并验证证书或直接上传对方公钥")
        if not signer_public_key.startswith('04') or len(signer_public_key) != 130:
            raise ValueError("对方公钥格式错误")
        
        x_hex = signer_public_key[2:66]
        y_hex = signer_public_key[66:]
        signer_public_key_tuple = (int(x_hex, 16), int(y_hex, 16))

        # 5. 使用对方公钥验证签名
        verify_result = sm2_verify(hash_hex, (r, s), signer_public_key_tuple)

        # 6. 显示验证结果
        verification_result_box.delete('1.0', tk.END)
        if verify_result:
            verification_result_box.insert(tk.END, "验证成功\n1. 密文未被修改\n2. 签名验证通过")
            print("验证成功")
        else:
            verification_result_box.insert(tk.END, "验证失败\n1. 密文未被修改\n2. 签名验证失败")
            print("验证失败")

    except ValueError as ve:
        print(f"验证错误: {ve}")
        verification_result_box.delete('1.0', tk.END)
        verification_result_box.insert(tk.END, f"验证失败: {str(ve)}")
        messagebox.showerror("错误", f"验证失败: {str(ve)}")
    except Exception as e:
        print(f"验证过程发生错误: {e}")
        verification_result_box.delete('1.0', tk.END)
        verification_result_box.insert(tk.END, f"验证失败: {str(e)}")
        messagebox.showerror("错误", f"验证失败: {e}")

def generate_ca_keys():
    """生成 CA 公私钥对，并显示在文本框中"""
    global ca_private_key, ca_public_key
    try:
        ca_private_key, ca_public_key = generate_key()
        ca_public_key_box.delete('1.0', tk.END)
        ca_private_key_box.delete('1.0', tk.END)
        ca_public_key_hex = f"04{hex(ca_public_key[0])[2:].zfill(64)}{hex(ca_public_key[1])[2:].zfill(64)}"
        ca_public_key_box.insert(tk.END, ca_public_key_hex)
        ca_private_key_box.insert(tk.END, hex(ca_private_key)[2:].zfill(64))
        messagebox.showinfo("成功", "CA公私钥生成成功")
        print("CA公私钥生成成功")
    except Exception as e:
        print(f"CA密钥生成失败: {e}")
        messagebox.showerror("错误", f"CA密钥生成失败: {e}")

def issue_certificate():
    """
    CA 用于给用户公钥颁发数字证书，
    证书中包含用户名、用户公钥、CA 公钥以及签名等信息
    """
    global issued_certificates, user_public_key_for_certificate, username_for_certificate
    try:
        # 检查 CA 密钥
        if not ca_private_key or not ca_public_key:
            raise ValueError("请先生成或加载CA密钥")
        if not user_public_key_for_certificate:
            raise ValueError("请先上传用户公钥")

        # 从输入框获取用户名
        username = ca_username_entry.get().strip()
        if not username:
            raise ValueError("请输入用户名")
        username_for_certificate = username

        # 计算用户公钥哈希
        user_public_key_hex = user_public_key_for_certificate
        user_hash = SHA256.new(user_public_key_hex.encode()).hexdigest()

        # 使用 CA 私钥对该哈希进行签名
        r, s = sm2_sign(user_hash, ca_private_key)
        signature = f"{r}{s}"

        # 生成数字证书
        certificate = {
            'username': username,
            'user_public_key': user_public_key_hex,
            'ca_public_key': f"04{hex(ca_public_key[0])[2:].zfill(64)}{hex(ca_public_key[1])[2:].zfill(64)}",
            'signature': signature
        }

        # 加入到已颁发列表并存储
        issued_certificates.append(certificate)
        save_certificate_repository()

        # 在 certificate_box 中显示所有证书
        certificate_box.delete('1.0', tk.END)
        for cert in issued_certificates:
            certificate_box.insert(tk.END,
                f"用户名: {cert['username']}\n"
                f"用户公钥: {cert['user_public_key']}\n"
                f"CA公钥: {cert['ca_public_key']}\n"
                f"签名: {cert['signature']}\n\n")

        print("数字证书颁发成功")
        messagebox.showinfo("成功", "数字证书颁发成功")
    except Exception as e:
        print(f"数字证书颁发失败: {e}")
        messagebox.showerror("错误", f"数字证书颁发失败: {e}")

def verify_certificate_func():
    """验证上传的数字证书是否由本 CA 签发，且未被篡改"""
    global issued_certificates, uploaded_certificate
    try:
        if not uploaded_certificate:
            raise ValueError("请先上传证书")
        if not ca_public_key:
            raise ValueError("请先生成或加载CA公钥")

        # 判断存储库中是否存在该证书
        if uploaded_certificate not in issued_certificates:
            raise ValueError("证书验证不通过：该用户不存在")

        # 提取证书信息
        username = uploaded_certificate.get('username', '未知')
        user_public_key_hex = uploaded_certificate['user_public_key']
        ca_public_key_hex = uploaded_certificate['ca_public_key']
        signature_str = uploaded_certificate['signature']

        # 计算用户公钥哈希
        user_hash = SHA256.new(user_public_key_hex.encode()).hexdigest()

        if len(signature_str) != 128:
            raise ValueError("签名格式错误，应为128字符（64字符r + 64字符s）")
        r = signature_str[:64]
        s = signature_str[64:]

        # 解析 CA 公钥（hex -> int 再组成元组）
        ca_public_key_tuple = (int(ca_public_key_hex[2:66], 16), int(ca_public_key_hex[66:], 16))

        # 使用 CA 公钥验证签名
        result = sm2_verify(user_hash, (r, s), ca_public_key_tuple)

        # 显示验证结果
        verification_result_box_ca.delete('1.0', tk.END)
        if result:
            verification_result_box_ca.insert(tk.END,
                f"证书验证通过\n用户名: {username}\n用户公钥: {user_public_key_hex}")
            print("证书验证通过")
        else:
            verification_result_box_ca.insert(tk.END, "证书验证失败：签名无效")
            print("证书验证失败：签名无效")
    except Exception as e:
        print(f"证书验证失败: {e}")
        messagebox.showerror("错误", f"证书验证失败: {e}")
        verification_result_box_ca.delete('1.0', tk.END)
        verification_result_box_ca.insert(tk.END, f"证书验证失败: {str(e)}")

def revoke_certificate_func():
    """撤销数字证书，将其从存储库中移除"""
    global issued_certificates
    try:
        # 从 certificate_box 获取当前显示的证书内容
        current_cert_text = certificate_box.get('1.0', tk.END).strip()
        if not current_cert_text:
            raise ValueError("当前没有显示的证书可撤销")

        # 解析证书内容
        lines = current_cert_text.split('\n')
        cert = {}
        for line in lines:
            if line.startswith("用户名: "):
                cert['username'] = line.split(': ', 1)[1]
            elif line.startswith("用户公钥: "):
                cert['user_public_key'] = line.split(': ', 1)[1]
            elif line.startswith("CA公钥: "):
                cert['ca_public_key'] = line.split(': ', 1)[1]
            elif line.startswith("签名: "):
                cert['signature'] = line.split(': ', 1)[1]

        if not cert:
            raise ValueError("无法解析当前证书")

        # 如果该证书不在存储库中，则无法撤销
        if cert not in issued_certificates:
            raise ValueError("该证书不存在于存储库，无法撤销")

        # 从列表中移除并更新到文件
        issued_certificates.remove(cert)
        save_certificate_repository()

        # 更新显示：清空并重新显示剩余证书
        certificate_box.delete('1.0', tk.END)
        for c in issued_certificates:
            certificate_box.insert(tk.END,
                f"用户名: {c['username']}\n"
                f"用户公钥: {c['user_public_key']}\n"
                f"CA公钥: {c['ca_public_key']}\n"
                f"签名: {c['signature']}\n\n")

        # 清空全局变量 uploaded_certificate
        global uploaded_certificate
        uploaded_certificate = None

        # 清空验证结果与对方公钥显示框
        verification_result_box_ca.delete('1.0', tk.END)
        signer_public_key_box.delete('1.0', tk.END)

        # 显示撤销结果
        revoke_result_box.delete('1.0', tk.END)
        revoke_result_box.insert(tk.END, "证书已撤销")

        print("证书撤销成功")
        messagebox.showinfo("成功", "证书撤销成功")
    except Exception as e:
        print(f"证书撤销失败: {e}")
        messagebox.showerror("错误", f"证书撤销失败: {e}")

def save_ca_keys_func():
    """将 CA 公私钥保存到文件"""
    try:
        if not ca_private_key or not ca_public_key:
            raise ValueError("请先生成CA密钥")

        # 选择保存目录
        save_dir = filedialog.askdirectory(title="选择CA密钥保存目录")
        if not save_dir:
            return

        if not os.path.exists(save_dir):
            os.makedirs(save_dir)

        # 保存 CA 公钥
        ca_public_key_hex = f"04{hex(ca_public_key[0])[2:].zfill(64)}{hex(ca_public_key[1])[2:].zfill(64)}"
        with open(os.path.join(save_dir, "ca_public_key.txt"), 'w') as pub_file:
            pub_file.write(ca_public_key_hex)

        # 保存 CA 私钥
        with open(os.path.join(save_dir, "ca_private_key.txt"), 'w') as priv_file:
            priv_file.write(hex(ca_private_key)[2:].zfill(64))

        messagebox.showinfo("成功", "CA公私钥已保存")
        print("CA公私钥已保存")
    except Exception as e:
        print(f"CA密钥保存失败: {e}")
        messagebox.showerror("错误", f"CA密钥保存失败: {e}")

def load_ca_public_key():
    """从文件加载 CA 公钥"""
    global ca_public_key
    try:
        ca_pub_key_path = filedialog.askopenfilename(title="选择CA公钥文件", filetypes=[("Text files", "*.txt")])
        if not ca_pub_key_path:
            return
        with open(ca_pub_key_path, 'r') as pub_file:
            ca_public_key_hex = pub_file.read().strip()
            if not ca_public_key_hex.startswith('04') or len(ca_public_key_hex) != 130:
                raise ValueError("CA公钥格式错误")
            ca_public_key_box.delete('1.0', tk.END)
            ca_public_key_box.insert(tk.END, ca_public_key_hex)
            ca_public_key = (int(ca_public_key_hex[2:66], 16), int(ca_public_key_hex[66:], 16))

        messagebox.showinfo("成功", "CA公钥加载成功")
        print("CA公钥加载成功")
    except Exception as e:
        print(f"CA公钥加载失败: {e}")
        messagebox.showerror("错误", f"CA公钥加载失败: {e}")

def load_ca_private_key():
    """从文件加载 CA 私钥"""
    global ca_private_key
    try:
        ca_priv_key_path = filedialog.askopenfilename(title="选择CA私钥文件", filetypes=[("Text files", "*.txt")])
        if not ca_priv_key_path:
            return
        with open(ca_priv_key_path, 'r') as priv_file:
            ca_private_key_hex = priv_file.read().strip()
            if len(ca_private_key_hex) != 64:
                raise ValueError("CA私钥格式错误")
            ca_private_key_box.delete('1.0', tk.END)
            ca_private_key_box.insert(tk.END, ca_private_key_hex)
            ca_private_key = int(ca_private_key_hex, 16)

        messagebox.showinfo("成功", "CA私钥加载成功")
        print("CA私钥加载成功")
    except Exception as e:
        print(f"CA私钥加载失败: {e}")
        messagebox.showerror("错误", f"CA私钥加载失败: {e}")

def upload_user_public_key():
    """
    从文件选择用户公钥文件，用于 CA 系统颁发证书时，
    加载并显示到 user_public_key_display_box
    """
    global user_public_key_for_certificate, user_public_key_display_box
    try:
        file_path = filedialog.askopenfilename(title="选择用户公钥文件", filetypes=[("Text files", "*.txt")])
        if not file_path:
            return
        with open(file_path, 'r') as pub_file:
            user_public_key_hex = pub_file.read().strip()
            if not user_public_key_hex.startswith('04') or len(user_public_key_hex) != 130:
                raise ValueError("用户公钥格式错误")
            user_public_key_display_box.delete('1.0', tk.END)
            user_public_key_display_box.insert(tk.END, user_public_key_hex)
            user_public_key_for_certificate = user_public_key_hex

            messagebox.showinfo("成功", "用户公钥上传成功")
            print("用户公钥上传成功")
    except Exception as e:
        print(f"用户公钥上传失败: {e}")
        messagebox.showerror("错误", f"用户公钥上传失败: {e}")

def upload_recipient_public_key():
    """在签名系统中上传接收者公钥文件"""
    global recipient_public_key_box
    try:
        file_path = filedialog.askopenfilename(title="选择接收者公钥文件", filetypes=[("Text files", "*.txt")])
        if not file_path:
            return
        with open(file_path, 'r') as pub_file:
            recipient_public_key_hex = pub_file.read().strip()
            if not recipient_public_key_hex.startswith('04') or len(recipient_public_key_hex) != 130:
                raise ValueError("接收者公钥格式错误")
            recipient_public_key_box.delete('1.0', tk.END)
            recipient_public_key_box.insert(tk.END, recipient_public_key_hex)

            messagebox.showinfo("成功", "接收者公钥上传成功")
            print("接收者公钥上传成功")
    except Exception as e:
        print(f"上传接收者公钥失败: {e}")
        messagebox.showerror("错误", f"上传接收者公钥失败: {e}")

def save_certificate():
    """将已颁发的数字证书（issued_certificates）列表保存为 txt 文件"""
    try:
        if not issued_certificates:
            raise ValueError("没有可保存的证书")

        file_path = filedialog.asksaveasfilename(defaultextension=".txt", filetypes=[("Text files", "*.txt")])
        if not file_path:
            return

        with open(file_path, 'w', encoding='utf-8') as file:
            for cert in issued_certificates:
                file.write(f"用户名: {cert['username']}\n")
                file.write(f"用户公钥: {cert['user_public_key']}\n")
                file.write(f"CA公钥: {cert['ca_public_key']}\n")
                file.write(f"签名: {cert['signature']}\n\n")

        messagebox.showinfo("成功", "证书保存成功")
        print("证书保存成功")
    except Exception as e:
        print(f"证书保存失败: {e}")
        messagebox.showerror("错误", f"证书保存失败: {e}")

def load_certificate():
    """
    从文件加载数字证书，并将其中的最后一个证书设置为 uploaded_certificate，
    同时在 certificate_box 中显示所有证书内容
    """
    global uploaded_certificate
    try:
        file_path = filedialog.askopenfilename(filetypes=[("Text files", "*.txt")])
        if not file_path:
            return

        with open(file_path, 'r', encoding='utf-8') as file:
            content = file.read().strip()
            certificates = content.split('\n\n')
            certificate_box.delete('1.0', tk.END)
            for cert_str in certificates:
                lines = cert_str.split('\n')
                if len(lines) < 4:
                    continue
                cert = {
                    'username': lines[0].split(': ', 1)[1],
                    'user_public_key': lines[1].split(': ', 1)[1],
                    'ca_public_key': lines[2].split(': ', 1)[1],
                    'signature': lines[3].split(': ', 1)[1]
                }
                certificate_box.insert(tk.END,
                    f"用户名: {cert['username']}\n"
                    f"用户公钥: {cert['user_public_key']}\n"
                    f"CA公钥: {cert['ca_public_key']}\n"
                    f"签名: {cert['signature']}\n\n")

                uploaded_certificate = cert  # 记录最后一个证书为已上传证书

        messagebox.showinfo("成功", "证书加载成功")
        print("证书加载成功")
    except Exception as e:
        print(f"证书加载失败: {e}")
        messagebox.showerror("错误", f"证书加载失败: {e}")

def load_certificate_verify():
    """在验证系统中加载证书并立即调用验证逻辑"""
    load_certificate()
    verify_certificate_and_extract_public_key(uploaded_certificate)

def verify_certificate_and_extract_public_key(certificate):
    """
    验证证书并提取用户公钥到 signer_public_key_box，
    用于验证对方的签名
    """
    try:
        if not ca_public_key:
            raise ValueError("请先生成或加载CA公钥")

        # 提取证书中的关键信息
        username = certificate.get('username', '未知')
        user_public_key_hex = certificate['user_public_key']
        ca_public_key_hex = certificate['ca_public_key']
        signature_str = certificate['signature']

        # 计算用户公钥哈希
        user_hash = SHA256.new(user_public_key_hex.encode()).hexdigest()

        # 分离 r 和 s
        if len(signature_str) != 128:
            raise ValueError("签名格式错误，应为128字符（64字符r + 64字符s）")
        r = signature_str[:64]
        s = signature_str[64:]

        # 解析 CA 公钥
        ca_public_key_tuple = (int(ca_public_key_hex[2:66], 16), int(ca_public_key_hex[66:], 16))

        # 验证签名
        is_valid = sm2_verify(user_hash, (r, s), ca_public_key_tuple)
        if is_valid:
            messagebox.showinfo("验证成功", f"证书验证通过\n用户名: {username}")
            print("证书验证通过")
            # 将提取到的用户公钥放到 signer_public_key_box
            signer_public_key_box.delete('1.0', tk.END)
            signer_public_key_box.insert(tk.END, user_public_key_hex)
        else:
            messagebox.showerror("验证失败", "证书验证失败：签名无效")
            print("证书验证失败：签名无效")
    except Exception as e:
        messagebox.showerror("验证错误", f"证书验证过程中发生错误: {e}")
        print(f"证书验证过程中发生错误: {e}")

def save_to_file():
    """将签名系统生成的数字签名和加密结果（密文）保存到文件"""
    try:
        if not signing_signature or not sm2_encrypt_box.get('1.0', tk.END).strip():
            raise ValueError("请先完成签名和加密")

        file_path = filedialog.asksaveasfilename(defaultextension=".txt", filetypes=[("Text files", "*.txt")])
        if not file_path:
            return

        with open(file_path, 'w', encoding='utf-8') as file:
            file.write(f"SM2签名: {signing_signature}\n")
            file.write(f"SM2加密结果: {sm2_encrypt_box.get('1.0', tk.END).strip()}\n")

        messagebox.showinfo("成功", "文件保存成功")
        print("文件保存成功")
    except Exception as e:
        print(f"文件保存失败: {e}")
        messagebox.showerror("错误", f"文件保存失败: {e}")

def load_signature_and_ciphertext_verification():
    """在验证系统中，从文件加载签名和密文，并显示到相应的文本框"""
    global verification_signature, verification_ciphertext
    try:
        file_path = filedialog.askopenfilename(filetypes=[("Text files", "*.txt")])
        if not file_path:
            return

        with open(file_path, 'r', encoding='utf-8') as file:
            lines = file.readlines()
            for line in lines:
                if line.startswith("SM2签名: "):
                    verification_signature = line.strip().split("SM2签名: ", 1)[1]
                    verification_signature_box.delete('1.0', tk.END)
                    verification_signature_box.insert(tk.END, verification_signature)
                elif line.startswith("SM2加密结果: "):
                    verification_ciphertext = line.strip().split("SM2加密结果: ", 1)[1]
                    sm2_decrypt_box.delete('1.0', tk.END)
                    sm2_decrypt_box.insert(tk.END, verification_ciphertext)

        messagebox.showinfo("成功", "数据加载成功")
        print("数据加载成功")
    except Exception as e:
        print(f"数据加载失败: {e}")
        messagebox.showerror("错误", f"数据加载失败: {e}")

def clear_signing_display():
    """清空签名系统界面和相关全局变量"""
    global private_key, public_key, signing_signature, hash_value
    user_id_entry.delete(0, tk.END)
    public_key_box.delete('1.0', tk.END)
    private_key_box.delete('1.0', tk.END)
    plain_text_box.delete('1.0', tk.END)
    recipient_public_key_box.delete('1.0', tk.END)
    sha_result_box.config(state='normal')
    sha_result_box.delete('1.0', tk.END)
    sha_result_box.config(state='disabled')
    sm2_result_box.delete('1.0', tk.END)
    sm2_encrypt_box.delete('1.0', tk.END)

    private_key = None
    public_key = None
    signing_signature = None
    hash_value = None
    print("签名系统内容已清空")
    messagebox.showinfo("成功", "签名系统内容已清空")

def clear_verification_display():
    """清空验证系统界面和相关全局变量"""
    global verification_signature, verification_ciphertext, uploaded_certificate
    private_key_box_verify.delete('1.0', tk.END)
    signer_public_key_box.delete('1.0', tk.END)
    sm2_decrypt_box.delete('1.0', tk.END)
    sm2_decrypt_box_result.delete('1.0', tk.END)
    verification_signature_box.delete('1.0', tk.END)
    hash_display_box.config(state='normal')
    hash_display_box.delete('1.0', tk.END)
    hash_display_box.config(state='disabled')
    verification_result_box.delete('1.0', tk.END)

    verification_signature = None
    verification_ciphertext = None
    uploaded_certificate = None
    print("验证系统内容已清空")
    messagebox.showinfo("成功", "验证系统内容已清空")

def clear_ca_display():
    """清空 CA 系统界面和相关全局变量"""
    global user_public_key_for_certificate, username_for_certificate, uploaded_certificate, ca_public_key, ca_private_key
    ca_username_entry.delete(0, tk.END)
    user_public_key_display_box.delete('1.0', tk.END)
    certificate_box.delete('1.0', tk.END)
    verification_result_box_ca.delete('1.0', tk.END)
    revoke_result_box.delete('1.0', tk.END)
    ca_public_key_box.delete('1.0', tk.END)
    ca_private_key_box.delete('1.0', tk.END)

    user_public_key_for_certificate = None
    username_for_certificate = ""
    uploaded_certificate = None
    ca_public_key = None
    ca_private_key = None
    print("CA系统内容已清空")
    messagebox.showinfo("成功", "CA系统内容已清空")

# ------------------ 以下是 GUI 界面布局与初始化 ------------------ #
root = tk.Tk()
root.title("数字签名与CA系统--by 甄五四and梁浩哲")
root.geometry("1600x900")  # 设置主窗口尺寸

icon_path = resource_path(os.path.join('resources', 'signature.ico'))
if os.path.exists(icon_path):
    try:
        root.iconbitmap(icon_path)
    except:
        print("无法加载图标文件。")

style = ttk.Style()
style.theme_use('clam')

main_frame = ttk.Frame(root)
main_frame.pack(fill='both', expand=True, padx=20, pady=20)

title_font = font.Font(family='Helvetica', size=24, weight='bold')
title_label = ttk.Label(main_frame, text="数字签名系统", font=title_font)
title_label.pack(pady=20)

notebook = ttk.Notebook(main_frame)
notebook.pack(fill='both', expand=True)

sign_frame = ttk.Frame(notebook)
verify_frame = ttk.Frame(notebook)
ca_frame = ttk.Frame(notebook)

notebook.add(sign_frame, text='签名系统')
notebook.add(verify_frame, text='验证系统')
notebook.add(ca_frame, text='CA系统')

# ------------------- 签名系统页面布局 -------------------
sign_content = ttk.Frame(sign_frame)
sign_content.pack(fill='both', expand=True, padx=20, pady=20)

left_panel = ttk.LabelFrame(sign_content, text="密钥管理")
left_panel.pack(side='left', fill='y', padx=(0,10))

ttk.Label(left_panel, text="用户ID：").pack(pady=5)
user_id_entry = ttk.Entry(left_panel)
user_id_entry.pack(pady=5)
ttk.Button(left_panel, text="生成密钥", command=lambda: generate_keys_with_id_signing(user_id_entry.get())).pack(pady=5)
ttk.Button(left_panel, text="保存密钥", command=save_user_keys).pack(pady=5)
ttk.Button(left_panel, text="加载用户私钥", command=load_user_keys_signing).pack(pady=5)

ttk.Label(left_panel, text="公钥：").pack(pady=5)
public_key_box = scrolledtext.ScrolledText(left_panel, width=50, height=4)
public_key_box.pack(pady=5)

ttk.Label(left_panel, text="私钥：").pack(pady=5)
private_key_box = scrolledtext.ScrolledText(left_panel, width=50, height=4)
private_key_box.pack(pady=5)

ttk.Button(left_panel, text="上传接收者公钥文件", command=upload_recipient_public_key).pack(pady=5)

middle_panel = ttk.LabelFrame(sign_content, text="操作区域")
middle_panel.pack(side='left', fill='both', expand=True, padx=10)

ttk.Label(middle_panel, text="明文信息：").pack(pady=5)
plain_text_box = scrolledtext.ScrolledText(middle_panel, height=4)
plain_text_box.pack(fill='x', pady=5)
ttk.Button(middle_panel, text="上传文件", command=load_plain_text_from_file).pack(pady=5)

ttk.Label(middle_panel, text="接收者公钥：").pack(pady=5)
recipient_public_key_box = scrolledtext.ScrolledText(middle_panel, height=2)
recipient_public_key_box.pack(fill='x', pady=5)

ttk.Label(middle_panel, text="SHA256哈希结果：").pack(pady=5)
sha_result_box = scrolledtext.ScrolledText(middle_panel, height=2, state='disabled')
sha_result_box.pack(fill='x', pady=5)

button_frame = ttk.Frame(middle_panel)
button_frame.pack(pady=10)
ttk.Button(button_frame, text="SM2加密", command=sm2_encrypt).pack(side='left', padx=5)
ttk.Button(button_frame, text="SHA哈希", command=sha_hash).pack(side='left', padx=5)
ttk.Button(button_frame, text="SM2签名", command=sm2_sign_h1).pack(side='left', padx=5)
ttk.Button(button_frame, text="保存到文件", command=save_to_file).pack(side='left', padx=5)

ttk.Button(middle_panel, text="清空", command=clear_signing_display).pack(pady=5)

right_panel = ttk.LabelFrame(sign_content, text="结果显示")
right_panel.pack(side='right', fill='y', padx=(10,0))

ttk.Label(right_panel, text="SM2加密结果（Base64）：").pack(pady=5)
sm2_encrypt_box = scrolledtext.ScrolledText(right_panel, width=50, height=2)
sm2_encrypt_box.pack(pady=5)

ttk.Label(right_panel, text="数字签名：").pack(pady=5)
sm2_result_box = scrolledtext.ScrolledText(right_panel, width=50, height=2)
sm2_result_box.pack(pady=5)

# ------------------- 验证系统页面布局 -------------------
verify_content = ttk.Frame(verify_frame)
verify_content.pack(fill='both', expand=True, padx=20, pady=20)

verify_left_panel = ttk.LabelFrame(verify_content, text="密钥与证书信息")
verify_left_panel.pack(side='left', fill='y', padx=(0,10))

ttk.Button(verify_left_panel, text="加载用户私钥", command=load_user_keys_verification).pack(pady=10)
ttk.Button(verify_left_panel, text="上传证书", command=load_certificate_verify).pack(pady=10)
ttk.Button(verify_left_panel, text="上传对方公钥", command=upload_signer_public_key).pack(pady=10)
ttk.Button(verify_left_panel, text="上传签名文件", command=load_signature_and_ciphertext_verification).pack(pady=10)

ttk.Label(verify_left_panel, text="私钥：").pack(pady=5)
private_key_box_verify = scrolledtext.ScrolledText(verify_left_panel, width=50, height=2)
private_key_box_verify.pack(pady=5)

ttk.Label(verify_left_panel, text="对方公钥：").pack(pady=5)
signer_public_key_box = scrolledtext.ScrolledText(verify_left_panel, width=50, height=4)
signer_public_key_box.pack(pady=5)

verify_middle_panel = ttk.LabelFrame(verify_content, text="验证操作")
verify_middle_panel.pack(side='left', fill='both', expand=True, padx=10)

ttk.Label(verify_middle_panel, text="密文（Base64）：").pack(pady=5)
sm2_decrypt_box = scrolledtext.ScrolledText(verify_middle_panel, height=3)
sm2_decrypt_box.pack(fill='x', pady=5)

ttk.Button(verify_middle_panel, text="验证签名", command=sm2_verify_signature).pack(pady=10)
ttk.Button(verify_middle_panel, text="解密密文", command=sm2_decrypt).pack(pady=10)
ttk.Button(verify_middle_panel, text="清空", command=clear_verification_display).pack(pady=5)

verify_right_panel = ttk.LabelFrame(verify_content, text="验证结果")
verify_right_panel.pack(side='right', fill='y', padx=(10,0))

ttk.Label(verify_right_panel, text="解密后的明文：").pack(pady=5)
sm2_decrypt_box_result = scrolledtext.ScrolledText(verify_right_panel, width=50, height=2)
sm2_decrypt_box_result.pack(pady=5)

ttk.Label(verify_right_panel, text="计算哈希：").pack(pady=5)
hash_display_box = scrolledtext.ScrolledText(verify_right_panel, width=50, height=2)
hash_display_box.pack(pady=5)

ttk.Label(verify_right_panel, text="签名：").pack(pady=5)
verification_signature_box = scrolledtext.ScrolledText(verify_right_panel, width=50, height=2)
verification_signature_box.pack(pady=5)

ttk.Label(verify_right_panel, text="验证结果：").pack(pady=5)
verification_result_box = scrolledtext.ScrolledText(verify_right_panel, width=50, height=3)
verification_result_box.pack(pady=5)

# ------------------- CA系统页面布局 -------------------
ca_content = ttk.Frame(ca_frame)
ca_content.pack(fill='both', expand=True, padx=20, pady=20)

ca_left_panel = ttk.LabelFrame(ca_content, text="CA密钥管理")
ca_left_panel.pack(side='left', fill='y', padx=(0,10))

ttk.Button(ca_left_panel, text="生成CA公私钥", command=generate_ca_keys).pack(pady=10)
ttk.Button(ca_left_panel, text="保存CA密钥", command=save_ca_keys_func).pack(pady=5)
ttk.Button(ca_left_panel, text="加载CA公钥", command=load_ca_public_key).pack(pady=5)
ttk.Button(ca_left_panel, text="加载CA私钥", command=load_ca_private_key).pack(pady=5)

ttk.Label(ca_left_panel, text="CA公钥：").pack(pady=5)
ca_public_key_box = scrolledtext.ScrolledText(ca_left_panel, width=50, height=4)
ca_public_key_box.pack(pady=5)

ttk.Label(ca_left_panel, text="CA私钥：").pack(pady=5)
ca_private_key_box = scrolledtext.ScrolledText(ca_left_panel, width=50, height=4)
ca_private_key_box.pack(pady=5)

ca_middle_panel = ttk.LabelFrame(ca_content, text="CA操作")
ca_middle_panel.pack(side='left', fill='both', expand=True, padx=10)

ttk.Label(ca_middle_panel, text="用户名：").pack(pady=5)
ca_username_entry = ttk.Entry(ca_middle_panel)
ca_username_entry.pack(pady=5)

ttk.Button(ca_middle_panel, text="上传用户公钥", command=upload_user_public_key).pack(pady=5)
ttk.Label(ca_middle_panel, text="已上传用户公钥：").pack(pady=5)
user_public_key_display_box = scrolledtext.ScrolledText(ca_middle_panel, width=50, height=2)
user_public_key_display_box.pack(pady=5)

ca_button_frame = ttk.Frame(ca_middle_panel)
ca_button_frame.pack(pady=10, fill='x')

ttk.Button(ca_button_frame, text="颁发数字证书", command=issue_certificate).grid(row=0, column=0, padx=5, pady=5, sticky='ew')
ttk.Button(ca_button_frame, text="验证数字证书", command=verify_certificate_func).grid(row=0, column=1, padx=5, pady=5, sticky='ew')
ttk.Button(ca_button_frame, text="撤销数字证书", command=revoke_certificate_func).grid(row=1, column=0, padx=5, pady=5, sticky='ew')
ttk.Button(ca_button_frame, text="保存证书", command=save_certificate).grid(row=1, column=1, padx=5, pady=5, sticky='ew')
ttk.Button(ca_button_frame, text="加载证书", command=load_certificate).grid(row=2, column=0, padx=5, pady=5, sticky='ew')
ttk.Button(ca_button_frame, text="清空", command=clear_ca_display).grid(row=2, column=1, padx=5, pady=5, sticky='ew')

ca_button_frame.grid_columnconfigure(0, weight=1)
ca_button_frame.grid_columnconfigure(1, weight=1)

ca_right_panel = ttk.LabelFrame(ca_content, text="CA结果显示")
ca_right_panel.pack(side='right', fill='y', padx=(10,0))

ttk.Label(ca_right_panel, text="用户数字证书：").pack(pady=5)
certificate_box = scrolledtext.ScrolledText(ca_right_panel, width=50, height=6)
certificate_box.pack(pady=5)

ttk.Label(ca_right_panel, text="验证结果：").pack(pady=5)
verification_result_box_ca = scrolledtext.ScrolledText(ca_right_panel, width=50, height=3)
verification_result_box_ca.pack(pady=5)

ttk.Label(ca_right_panel, text="撤销结果：").pack(pady=5)
revoke_result_box = scrolledtext.ScrolledText(ca_right_panel, width=50, height=3)
revoke_result_box.pack(pady=5)

bg_image_path = resource_path('./resources/1.jpg')
if os.path.exists(bg_image_path):
    try:
        bg_image = Image.open(bg_image_path)
        bg_image = resize_image(bg_image, (1600, 900))  # 根据 Pillow 版本兼容使用
        bg_photo = ImageTk.PhotoImage(bg_image)
        root.bg_photo = bg_photo  # 防止被垃圾回收
        bg_label = tk.Label(root, image=bg_photo)
        bg_label.place(x=0, y=0, relwidth=1, relheight=1)
        bg_label.lower()
    except Exception as e:
        print(f"加载背景图片失败: {e}")

# 启动前先加载证书存储库
load_certificate_repository()

root.mainloop()
