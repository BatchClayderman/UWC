try:
	import os
	import sys
	from shutil import rmtree
	from math import log10 as log
	from threading import current_thread, Lock, Thread
	from re import findall
	from datetime import date, datetime, timedelta
	from time import strftime, localtime, sleep
	from tkinter.filedialog import askopenfilenames, askdirectory
	from tkinter.messagebox import showerror, askokcancel, showinfo
	from tkinter.ttk import Combobox, Progressbar
	from tkinter import *
	os.chdir(os.path.abspath(os.path.dirname(__file__)))#解析进入当前目录
except:
	input("[!] System: Error loading <built-in> libraries. \n[-] Please make sure you have installed Python correctly. \n[-] Press <Enter> to exit. \n")
	sys.exit(-2)# EEOF



# System（系统性）全局变量
EXIT_SUCCESS = 0#操作成功结束
EXIT_FAILURE = 1#失败
EOF = (-1)#意外中止
EEOF = (-2)#更严重的中止事件
sleep_time = 5
new_lines = 5
system_print_lock = Lock()
system_msgbox_lock = Lock()
thread_splitter_lock = Lock()
thread_similarity_lock = Lock()
thread_sentiment_lock = Lock()


# Environment 全局变量
Global_Title = "Universal Word Calculator"
WinOS = (__import__("platform").system().lower() == "windows")
UAC = False
environment_requirements = (							\
	("<built-in>", "jieba", "snownlp", "python-docx", "pdfminer"), 			\
	("numpy", "pandas", "matplotlib", "wordcloud", "chinesecalendar")		\
)
environment_checksum = {										\
	"<built-in>":"pass", 										\
	"jieba":"import jieba", 									\
	"snownlp":"from snownlp import SnowNLP, sentiment", 						\
	"python-docx":"import docx", 									\
	"pdfminer":"\n".join(["from pdfminer.pdfinterp import PDFPageInterpreter, PDFResourceManager", 		\
		"from pdfminer.converter import PDFPageAggregator", 					\
		"from pdfminer.layout import LAParams", 						\
		"from pdfminer.pdfparser import PDFParser", 						\
		"from pdfminer.pdfdocument import PDFDocument", 					\
		"from pdfminer.pdfpage import PDFPage"							\
	]), 											\
												\
	"numpy":"from numpy import nan, nansum, nanmean, nanstd, array", 					\
	"pandas":"from pandas import DataFrame as DF, read_excel", 						\
	"matplotlib":"from matplotlib import ticker, pyplot as plt, use", 						\
	"wordcloud":"from wordcloud import WordCloud", 							\
	"chinesecalendar":"from chinese_calendar import is_holiday"						\
}
environment_state = {							\
	"<built-in>":1, "jieba":0, "snownlp":0, "python-docx":0, "pdfminer":0, 		\
	"numpy":0, "pandas":0, "matplotlib":0, "wordcloud":0, "chinesecalendar":0		\
}
environment_global = "jieba, SnowNLP, sentiment, WordCloud, docx, PDFPageInterpreter, PDFResourceManager, PDFPageAggregator, LAParams, PDFParser, PDFDocument, PDFPage, nan, nansum, nanmean, nanstd, array, DF, read_excel, ticker, plt, use, is_holiday"
class Environment_State:
	environment_satisfy_lock = Lock()
	environment_satisfy = False
	@staticmethod
	def get():
		Environment_State.environment_satisfy_lock.acquire()
		tmp = Environment_State.environment_satisfy
		Environment_State.environment_satisfy_lock.release()
		return tmp
	@staticmethod
	def set(state):
		Environment_State.environment_satisfy_lock.acquire()
		Environment_State.environment_satisfy = state
		Environment_State.environment_satisfy_lock.release()
environment_satisfy = lambda:Environment_State.get()


# Config 全局变量
config_threading = Lock()
config_calculating = Lock()
config_occupied = 0
config_paths = {"data":"data", "sample":"sample", "ttf":"simkai.ttf", "pos":["pos.txt"], "neg":["neg.txt"], "not":["not.txt"], "userdict":["userdict_{0}.txt".format(i) for i in range(4)], "stopwords":["stopwords.txt"], "bad":["bad.txt"]}
config_modes = {"mode":0, "log":"nul", "output":"result"}
config_values = ("0 = precise_cut", "1 = cut_all", "2 = for_search", "3 = use_paddle")
config_displayers = {"data":None, "sample":None, "ttf":None, "pos":None, "neg":None, "not":None, "userdict":None, "stopwords":None, "bad":None}
config_controllers = set()
config_userdict_loaded = False#是否已加载过字典
config_calculated_dicts = {}#存储分词结果的字典（用于加速）
config_ori_std = sys.stdout#原始输出
config_stdout = config_ori_std#当前输出
config_chkrvs = lambda x:os.path.splitext(x)[0] not in ["nul", "prn", "con", "aux"] + ["com{0}".format(i) for i in range(10)] + ["lpt{0}".format(i) for i in range(10)]
config_gatherchars = lambda:set(config_paths["data"] + config_paths["sample"] + config_modes["output"])
config_chkdir = lambda:(						\
	(							\
		":" not in config_gatherchars()				\
		and "*" not in config_gatherchars()			\
		and "?" not in config_gatherchars()			\
		and "\"" not in config_gatherchars()			\
		and "<" not in config_gatherchars()			\
		and ">" not in config_gatherchars()			\
		and "|" not in config_gatherchars()			\
		and "\t" not in config_gatherchars()			\
		and "\r" not in config_gatherchars()			\
		and "\n" not in config_gatherchars()			\
	)#禁用保留符号（相对路径需要用到的除外）			\
	and							\
	(							\
		config_paths["data"] != config_paths["sample"]		\
		and config_paths["data"] != config_modes["output"]		\
		and config_paths["sample"] != config_modes["output"]	\
	)#目录要两两不同						\
	and							\
	(							\
		config_chkrvs(config_paths["data"])			\
		and config_chkrvs(config_paths["sample"])		\
		and config_chkrvs(config_modes["output"])		\
	)#禁用保留文件名						\
)
assert(config_chkdir())


# Splitter 全局变量
splitter_paths = {"file":"splitter.csv", "folder":"splitter", "wordcloud":"splitter.png"}
splitter_clears = {"space":True, "digits":True, "stopwords":True}
splitter_controllers = set()
splitter_draw_configs = {"width":2000, "height":1000, "background_color":"white"}#最大值 65535
splitter_gram_N = [i for i in range(1, 10)]
splitter_gatherchars = lambda:set(splitter_paths["file"] + splitter_paths["folder"] + splitter_paths["wordcloud"])
splitter_chkdir = lambda:(							\
	(								\
		":" not in splitter_gatherchars()					\
		and "*" not in splitter_gatherchars()				\
		and "?" not in splitter_gatherchars()				\
		and "\"" not in splitter_gatherchars()				\
		and "<" not in splitter_gatherchars()				\
		and ">" not in splitter_gatherchars()				\
		and "|" not in splitter_gatherchars()				\
		and "\t" not in splitter_gatherchars()				\
		and "\r" not in splitter_gatherchars()				\
		and "\n" not in splitter_gatherchars()				\
	)#禁用保留符号（相对路径需要用到的除外）				\
	and								\
	(								\
		splitter_paths["file"] != splitter_paths["folder"]			\
		and splitter_paths["file"] != splitter_paths["wordcloud"]		\
		and splitter_paths["folder"] != splitter_paths["wordcloud"]		\
	)#目录要两两不同							\
	and								\
	(								\
		config_chkrvs(splitter_paths["file"])				\
		and config_chkrvs(splitter_paths["folder"])				\
		and config_chkrvs(splitter_paths["wordcloud"])			\
	)#禁用保留文件名							\
)
assert(splitter_chkdir())


# Similarity 全局变量
similarity_values = ("0 = walk", "1 = filename", "2 = source", "3 = time")#比较顺序
similarity_paths = {"file":"similarity.csv", "folder":"similarity"}
similarity_clears = {"space":True, "digits":True, "stopwords":True}
similarity_configs = {"order":3, "gram_N":[i for i in range(1, 10)], "splitter":"|", "background_color":"white"}#最大值 65535
similarity_controllers = set()
similarity_embeddings_1, similarity_embeddings_2 = None, None#用于加速运算
similarity_idf = {}#存储词数
similarity_gatherchars = lambda:set(similarity_paths["file"] + similarity_paths["folder"])
similarity_chkdir = lambda:(						\
	(							\
		":" not in similarity_gatherchars()			\
		and "*" not in similarity_gatherchars()			\
		and "?" not in similarity_gatherchars()			\
		and "\"" not in similarity_gatherchars()			\
		and "<" not in similarity_gatherchars()			\
		and ">" not in similarity_gatherchars()			\
		and "|" not in similarity_gatherchars()			\
		and "\t" not in similarity_gatherchars()			\
		and "\r" not in similarity_gatherchars()			\
		and "\n" not in similarity_gatherchars()			\
	)#禁用保留符号（相对路径需要用到的除外）			\
	and							\
	(							\
		similarity_paths["file"] != similarity_paths["folder"]		\
	)#目录要两两不同						\
	and							\
	(							\
		config_chkrvs(splitter_paths["file"])			\
	)#禁用保留文件名						\
)
assert(similarity_chkdir())


# Sentiment 全局变量
sentiment_paths = {"file":"sentiment.csv", "folder":"sentiment"}
sentiment_config = "None"
sentiment_fill = True
sentiment_clears = {"space":True, "digits":True, "stopwords":True}
sentiment_values = (								\
	"None", 					#否定词关闭		\
	*("+{0}".format(i) for i in range(1, 6)), 		#后移			\
	*("-{0}".format(i) for i in range(1, 6)), 		#前移			\
	*("±{0}".format(i) for i in range(1, 6)), 		#前后区间		\
	"Per Unit"					#情感单元		\
)#否定词方式
sentiment_controllers = set()


# Viewer 全局变量（控制外观的参数）
frame_width = 36
frame_pad = 5
title_font = ("Times New Roman", 16, "bold")
title_fg = "red"
sub_pad = 2
label_font = ("Times New Roman", 12)
button_font = ("Times New Roman", 12)
state_fg = {None:"black", -1:"orange", 0:"blue", 1:"#00EE00"}
grid_pad = 5
state_symbols = {None:"[-]", -1:"[!]", 0:"[*]", 1:"[V]"}
entry_width = 13
progressbar_width = 640 + (entry_width << 1) + (grid_pad << 2)
clear_to = "。"



# System（系统性）子函数
def print_safe(strings, sep = " ", end = "\n", file = None, flush = False, *args):#具有互斥锁的 print() 函数
	if system_print_lock.locked() and "MainThread" == current_thread().name:#主线程用户消息抢占
		print(strings, *args, sep = sep, end = end, file = config_stdout if file is None else file, flush = flush)
		return
	system_print_lock.acquire()
	print(strings, *args, sep = sep, end = end, file = config_stdout if file is None else file, flush = flush)
	system_print_lock.release()

def MessageBox(strings, box_type = None):
	if box_type in state_symbols:
		system_msgbox_lock.acquire()#先加锁消息盒子再加锁打印
		if 0 == box_type:
			system_print_lock.acquire()
		print("{0} Message: {1}".format(state_symbols[box_type], strings))
		msgtmp = {-1:showerror, 0:askokcancel, 1:showinfo}[box_type](title = Global_Title, message = strings)
		if 0 == box_type:#询问类型的对话框打印答案
			print("{0} The answer is \"{1}\". ".format(state_symbols[None], "OK" if msgtmp else "Cancel"))
			system_print_lock.release()
		system_msgbox_lock.release()
		return msgtmp
	else:
		print_safe("{0} Message: KeyError({1}) has been caught. ".format(state_symbols[-1], box_type))
		return None

def ElevatePrivileges():
	if WinOS:
		if UAC:
			#os.system("mshta vbscript createobject(\"shell.application\").shellexecute(\"{0}\",\"\"\"{1}\"\"\",\"runas\",\"\",\"1\")(window.close)".format(sys.executable, os.path.abspath(__file__)))
			if 42 == __import__("ctypes").windll.shell32.ShellExecuteW(None, "runas", sys.executable, "\"{0}\"".format(os.path.abspath(__file__)), None, 1):#发起提权
				try:
					tk.destroy()#尝试销毁窗体
				except:
					pass
				print_safe("{0} Message: Process would exit as the new process would work instead of the old one. ".format(state_symbols[1]))
				print_safe("{0} Message: This window would be closed automatically in {1} second(s). ".format(state_symbols[None], sleep_time))
				sleep(sleep_time)
				sys.exit(EOF)#提权成功结束
			else:
				print_safe("{0} Message: Elevating privileges has been cancelled. ".format(state_symbols[None]))
	else:
		os.system("sudo \"{0}\" \"{1}\"".format(sys.executable, os.path.abspath(__file__)))

def OnCloseMainWindow():
	if thread_splitter_lock.locked() and thread_similarity_lock.locked() and thread_sentiment_lock.locked():#没有在运行的线程
		tk.destroy()
	elif MessageBox("Threads running, are you sure to exit forcibly? \n{0} Some results might be lost. \n{0} {1}".format(state_symbols[None], datetime.now().strftime("%Y-%m-%d %H:%M:%S")), 0):
		Environment_State.set(None)
		tk.destroy()


# Environment 子函数
def fix(library):
	commandline = "\"{0}\" -m pip install {1} -i \"https://pypi.tuna.tsinghua.edu.cn/simple\"".format(sys.executable, library)
	if UAC:#需要提权
		#os.system("mshta vbscript createobject(\"shell.application\").shellexecute(\"{0}\".format(sys.executable),\"-m pip install {0} -i \"https://pypi.tuna.tsinghua.edu.cn/simple\"\",\"runas\",\"\",\"1\")(window.close)".format(library))
		if 42 == __import__("ctypes").windll.shell32.ShellExecuteW(None, "runas", sys.executable, "-m pip install {0} -i \"https://pypi.tuna.tsinghua.edu.cn/simple\"".format(library), None, 1):
			print_safe("{0} Environment: Please wait while executing \"{1}\" as adminitrator. ".format(state_symbols[0], commandline.replace("\"", "\\\"")))
		else:
			print_safe("{0} Environment: Elevating privileges has been cancelled. ".format(state_symbols[None]))
	else:#某些系统没有提权的操作
		print_safe("{0} Environment: Please wait while executing \"{1}\". ".format(state_symbols[0], commandline.replace("\"", "\\\"")))
		os.system(commandline)

def check(library, alert = True):#检查单独环境（alert 为真表示需要弹窗并输出更多一些的信息）
	if environment_state[library] == 1:
		if alert:
			MessageBox("(^_^) The library \"{0}\" has already been checked. ".format(library), 1)
	else:
		environment_btn[library]["state"] = DISABLED
		environment_btn[library]["text"] = "checking"
		tk.update()
		try:
			if alert:
				print_safe("{0} Environment: Library \"{1}\" is being checked, please wait. ".format(state_symbols[0], library))
			exec(environment_checksum[library])
			environment_state[library] = 1
			environment_btn[library]["text"] = "checked"
			environment_btn[library]["fg"] = state_fg[1]
			print_safe("{0} Environment: Library \"{1}\" is ready. ".format(state_symbols[1], library))
		except:
			environment_state[library] = -1
			print_safe("{0} Environment: Library \"{1}\" is required, try fixing it. ".format(state_symbols[-1], library))
			if alert and MessageBox("Missing \"{0}\", press \"OK\" if you would like to have it fixed automatically. ".format(library), 0):
				fix(library)
			environment_btn[library]["text"] = "retry"
			environment_btn[library]["fg"] = state_fg[-1]
		environment_btn[library]["state"] = NORMAL

def checkall():#检查所有环境
	if environment_satisfy():
		MessageBox("(^_^) All the requirements are met. \n{0} All the child threads are hung up now. \n{0} Press either of the following buttons to continue. ".format(state_symbols[None]), 0)
	elif environment_satisfy() is None:
		print_safe("{0} Environment: The emergency button is pressed. ".format(state_symbols[-1]))
		sys.exit(EXIT_FAILURE)
	elif MessageBox("It might take a while to check out all the requirements. Press \"OK\" to continue. ", 0):
		environment_btn[None]["state"] = DISABLED
		environment_btn[None]["text"] = "Checking"
		tk.update()
		print_safe("{0} Environment: Checking and loading related packages, please wait. This may take a while. ".format(state_symbols[0]))
		for key in list(environment_checksum.keys()):
			check(key, False)
		for value in list(environment_state.values()):
			if value != 1:#只要有一个环境不满足就直接非自然中断
				environment_btn[None]["text"] = "Retry"
				environment_btn[None]["fg"] = state_fg[-1]
				print_safe("{0} Environment: Some packages do not meet the requirements. ".format(state_symbols[-1]))
				break
		else:#循环自然结束
			exec("\n".join(["global " + environment_global] + list(environment_checksum.values())))#务必在同一个 exec() 内
			for value in environment_global.split(", "):
				print_safe(state_symbols[None], end = " ")
				exec("print_safe({0})".format(value))
			Environment_State.set(True)#设置为 True
			environment_btn[None]["text"] = "Checked"
			environment_btn[None]["fg"] = state_fg[1]
			environment_state_label["text"] = "Ready"
			environment_state_label["fg"] = state_fg[1]
			splitter_btn_run["fg"] = state_fg[1]
			similarity_btn_run["fg"] = state_fg[1]
			sentiment_btn_run["fg"] = state_fg[1]
			print_safe("{0} Environment: All the packages are ready. ".format(state_symbols[1]))
		environment_btn[None]["state"] = NORMAL


# Config 子函数
def config_stdout_close():#关闭 log 文件
	try:
		if config_stdout != config_ori_std:
			config_stdout.close()
	except:
		pass

def config_ety_change_log(event):#修改 log 配置信息
	if config_ety_sv_log.get() != config_modes["log"]:#作出了修改
		config_modes["log"] = config_ety_sv_log.get()
		global config_stdout
		if config_modes["log"] and config_chkrvs(config_modes["log"]):#非控制台
			print_safe("{0} Config: The log has been changed to \"{1}\". ".format(state_symbols[1], config_modes["log"]))#先在控制台上进行输出
			if config_stdout == config_ori_std:#在控制台
				print_safe("{0} - End of Console - {1}".format(Global_Title, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
			else:
				print_safe("{0} - End of Log - {1}".format(Global_Title, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
			whether_new_lines = new_lines if os.path.exists(config_modes["log"]) else 0
			try:
				config_stdout_close()#关闭文件
				config_stdout = open(config_modes["log"], "a", encoding = "utf-8")
				print_safe("{0}{1} - Beginning of Log - {2}".format("\n" * whether_new_lines, Global_Title, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
			except Exception as change_log_exception:
				config_stdout_close()#关闭文件
				config_stdout = config_ori_std
				print_safe("{0} Config: Can not change log file since \"{1}\". ".format(state_symbols[-1], change_log_exception))
				MessageBox("Can not change log file. The output would be show in the console. ", -1)
		else:#控制台
			print_safe("{0} - End of Log - {1}".format(Global_Title, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
			config_stdout_close()#关闭文件
			config_modes["log"] = "nul"
			config_stdout = config_ori_std
			config_ety_sv_log.set(config_modes["log"])
			print_safe("{0} - Beginning of Console - {1}".format(Global_Title, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
			print_safe("{0} Config: The would be show in the console. ".format(state_symbols[1], config_modes["log"]))

def config_ety_change_output(event):#修改 output 配置信息
	reset_default_path = "result"
	rollback = config_modes["output"]
	config_modes["output"] = config_ety_sv_output.get()
	if rollback != config_modes["output"]:#作出了修改
		i, j = 0, len(config_modes["output"]) - 1
		if j < 0: config_modes["output"] = reset_default_path#空串
		while config_modes["output"][i] == " " and i < j: i += 1#定位到前面的第一个非空格字符
		while config_modes["output"][j] == " " and j > 0: j -= 1#定位到后面的最后一个非空格字符
		config_modes["output"] = config_modes["output"][i:j + 1]#截取片段
		reset_default_flag = False
		if not config_modes["output"]:#去除头尾空格后空串
			config_modes["output"] = reset_default_path
			reset_default_flag = True
		if config_chkdir():
			config_ety_sv_output.set(config_modes["output"])
			print_safe("{0} Config: Path of \"output\" has been {1} \"{2}\". ".format(state_symbols[1], "reset to default folder" if reset_default_flag else "changed to", config_modes["output"]))
		else:
			config_modes["output"] = rollback
			MessageBox("Folders of data, sample, and output should be different with each others. Special characters are not allowed. ", -1)
			config_ety_sv_output.set(rollback)# 回滚文字

def load_single_config(target, all_configs_flag):
	exec(															\
		(														\
			"global config_{0}"												\
			+ "{1}" + "config_{0} = set()"											\
			+ "{1}" + "for single_config_path in config_paths[\"{0}\"]:"#获取停用词表						\
			+ "{1}{2}" + "filepath = os.path.join(config_paths[\"sample\"], single_config_path)"						\
			+ "{1}{2}" + "content = getTxt(filepath)"										\
			+ "{1}{2}" + "if content is None:"										\
			+ "{1}{2}{2}" + "print_safe(\"{{0}} Config: Error loading \\\"{{1}}\\\". \".format(state_symbols[None], filepath))"			\
			+ "{1}{2}{2}" + "all_configs_flag[0] = False"									\
			+ "{1}{2}" + "else:"												\
			+ "{1}{2}{2}" + "print_safe(\"{{0}} Config: Successfully loaded \\\"{{1}}\\\". \".format(state_symbols[None], filepath))"		\
			+ "{1}{2}{2}" + "config_{0}.update(set(content.split(\"\\n\")))"							\
		).format(target, "\n", "\t")												\
	)

def config_load_userdict(any_prompt):#加载词典
	global config_userdict_loaded
	if config_userdict_loaded:
		print_safe("{0} {1}: Userdicts have been loaded before. ".format(state_symbols[1], any_prompt))
	config_userdict_flag = True#用于判断是否完全加载成功
	for ud in config_paths["userdict"]:
		lud = os.path.join(config_paths["sample"], ud)
		try:
			jieba.load_userdict(lud)
		except Exception as config_load_userdict_exception:
			config_userdict_flag = False
			print_safe("{0} {1}: Error loading \"{2}\" since {3}. ".format(state_symbols[-1], any_prompt, ud, config_load_userdict_exception))
	if config_userdict_flag:
		print_safe("{0} {1}: Userdicts have been loaded successfully. ".format(state_symbols[1], any_prompt))
		config_userdict_loaded = True
	else:
		config_userdict_loaded = False#设置为未加载
		if not MessageBox("One or more userdict config files could not be loaded, would you like to continue?", 0):
			return False
	return True

def load_all_configs():#加载配置文件
	print_safe("{0} Config: Begin to load all the configs. ".format(state_symbols[0]))
	all_configs_flag = [True]#使用列表作为形参时直接改地址
	for target in ("pos", "neg", "not", "stopwords", "bad"):#遍历所有配置
		load_single_config(target, all_configs_flag)
	if all_configs_flag[0]:
		print_safe("{0} Config: All the configs are loaded. ".format(state_symbols[1]))
	else:
		MessageBox("Some of the config files could not be loaded. Some related sets may be set empty. ", -1)

def config_lock_set(locker):
	config_threading.acquire()#多线程加锁
	global config_occupied
	if locker:#设置启用
		config_ety_change_log(None)
		config_ety_change_output(None)
		config_occupied -= 1#占用数量减少
		if 0 == config_occupied:#无占用则激活相关（孙）子窗体控件
			for controller in config_controllers:
				controller["state"] = NORMAL
			config_combobox["state"] = "readonly"
	else:#设置禁用
		if 0 == config_occupied:#无冻结相关（孙）子窗体控件则执行冻结
			for controller in config_controllers:
				controller["state"] = DISABLED
			config_combobox["state"] = DISABLED
			load_all_configs()#加载配置
		config_occupied += 1#占用数量增加
	tk.update()
	config_threading.release()#多线程解锁

def getpath(config_key):
	if config_key in ("data", "sample", "output"):#获取目录
		folderpath = askdirectory(initialdir = os.path.join(os.getcwd(), config_paths[config_key]))#获取目录
		if folderpath:#目录有效
			folderpath = os.path.relpath(folderpath, os.getcwd()).replace(os.sep, "/")#取相对路径并统一路径分隔符
			if (folderpath.lower() == config_paths[config_key].lower() if WinOS else folderpath == config_paths[config_key]):#与原目录相同
				return False
			else:
				rollback = config_paths[config_key]
				config_paths[config_key] = folderpath
				if config_chkdir():#没有重复目录
					config_displayers[config_key].set(folderpath)
					config_calculating.acquire()
					config_calculated_dicts.clear()#配置改变则清除缓存
					config_calculating.release()
					if "userdict" == config_key:
						global config_userdict_loaded
						config_userdict_loaded = False#重新选定了词典
					print_safe("{0} Config: Path of \"{1}\" has been changed to \"{2}\". ".format(state_symbols[1], config_key, folderpath))
					return True
				else:#有重复目录
					config_paths[config_key] = rollback#回滚
					MessageBox("Folders of data, sample, and output should be different with each others. Special characters are not allowed. ", -1)
		else:#选择了取消
			return False
	else:
		sample_abs = os.path.join(os.getcwd(), config_paths["sample"]).replace(os.sep, "/").lower() if WinOS else os.path.join(os.getcwd(), config_paths["sample"]).replace(os.sep, "/")# Sample 的绝对路径
		filepaths = list(askopenfilenames(initialdir = sample_abs, filetypes = [("ttf file", ".ttf")] if config_key == "ttf" else [("text files", ".txt"), ("all files", ".*")]))
		if len(filepaths) <= 0:
			return False
		for i in range(len(filepaths)):
			filepath = filepaths[i].replace(os.sep, "/")
			if ((filepath.lower() if WinOS else filepath).startswith(sample_abs)):
				filepaths[i] = filepath[len(sample_abs) + 1:]
			else:
				MessageBox("所选择的配置文件不位于 sample 目录路径下，如需使用该配置文件，请移动该文件至 sample 目录下，或修改 sample 目录路径。", -1)
				return False
		else:
			filepaths = filepaths[0] if config_key == "ttf" else filepaths
			if (str(filepaths).lower() == str(config_paths[config_key]).lower() if WinOS else filepaths == config_paths[config_key]):
				return False
			else:
				config_paths[config_key] = filepaths
				config_displayers[config_key].set(str(filepaths))
				print_safe("{0} Config: Path of \"{1}\" has been changed to {2}. ".format(state_symbols[1], config_key, filepaths))
				config_calculating.acquire()
				config_calculated_dicts.clear()#配置改变则清除缓存
				config_calculating.release()
				return True

def set_split_method(event):
	if config_modes["mode"] != int(config_split_sv.get()[0]):
		config_modes["mode"] = int(config_split_sv.get()[0])
		config_calculating.acquire()
		config_calculated_dicts.clear()#分词模式改变则清除缓存
		config_calculating.release()
		print_safe("{0} Config: Split method has been changed to \"{1}\". ".format(state_symbols[1], config_values[config_modes["mode"]]))


# Dispose 子函数
def getTxt(filepath, index = 0):#获取 .txt 文本内容
	coding = ("utf-8", "gbk", "utf-16")#目前常见且 Python 支持的编码
	if 0 <= index < len(coding):#索引范围内
		try:
			with open(filepath, "r", encoding = coding[index]) as f:
				content = f.read()
			return content[1:] if content.startswith("\ufeff") else content#如果是带有 BOM 的 utf-8 需要去掉 BOM
		except (UnicodeError, UnicodeDecodeError):
			return getTxt(filepath, index + 1)#递归
		except:
			return None
	else:
		return None#超出索引范围

def getDocx(filepath):#获取 .docx 文本内容
	docx_object = docx.Document(filepath)
	fullText = []
	for i in docx_object.paragraphs:#迭代 docx 文档里面的每一个段落
		fullText.append(i.text)#保存每一个段落的文本
	return "\n".join(fullText)

def getPdf(filepath):#获取 .pdf 文本内容
	fp = open(filepath, "rb")#以二进制读取模式打开 pdf 文档
	parser = PDFParser(fp)#创建一个与文档相关的解释器
	doc = PDFDocument(parser = parser)
	parser.set_document(doc = doc)#连接 pdf 文档对象与解释器
	doc._initialize_password()#如果是加密文档则请求输入密码
	resource = PDFResourceManager()#创建 pdf 资源管理器
	laparam = LAParams()#参数分析器
	device = PDFPageAggregator(resource, laparams = laparam)#创建一个聚合器
	interpreter = PDFPageInterpreter(resource, device)#创建 pdf 页面解释器
	content = ""#保存页面信息
	for page in PDFPage.get_pages(fp):
		interpreter.process_page(page)#使用页面解释器来读取内容
		layout = device.get_result()#使用聚合器来获取内容
		for out in layout:
			if hasattr(out, "get_text"):
				content += out.get_text().replace("\r", "").replace("\n", "")#排除断层（或不使用此行代码而使用下面两行代码）
				#pdf_tmp = out.get_text()
				#content += pdf_tmp[:-1] if pdf_tmp.endswith("\r") or pdf_tmp.endswith("\n") else pdf_tmp
	fp.close()
	return content

def getExcel(filepath, index_columns = None):#获取 excel 文件内容
	try:
		pf = read_excel(filepath)
	except:
		return None
	if index_columns is None:
		cols = [list(pf.columns)[0]]
	elif type(index_columns) in (tuple, list, set):
		cols = index_columns
	else:
		cols = [index_columns]
	content = ""
	for col in cols:
		content += "\n".join([str(item) for item in pf[col].tolist()])
	return content

def getContent(filepath):#获取文件文本内容
	support_dicts = {".txt":getTxt, ".csv":getTxt, ".docx":getDocx, ".pdf":getPdf, ".xlsx":getExcel, ".xls":getExcel, ".xlsm":getExcel}
	extension = os.path.splitext(filepath.lower())[1].lower()
	if extension in support_dicts:
		try:
			return support_dicts[extension](filepath)
		except:
			return None
	else:
		return None

def dispose(filepath, any_clears, force_update = False, do_not_store = False):#分词
	if type(any_clears) == int and 0 <= any_clears <= 7:
		dispose_intelligence = any_clears
	else:
		dispose_intelligence = "{0}|{1}".format(					\
			(0b000							\
				| 0b001 if any_clears["space"].get() else 0b000		\
				| 0b010 if any_clears["digits"].get() else 0b000		\
				| 0b100 if any_clears["stopwords"].get() else 0b000		\
			), 							\
			filepath							\
		)

	config_calculating.acquire()
	if not force_update and dispose_intelligence in config_calculated_dicts:#如果库里有且不用强制更新则直接返回
		cut = config_calculated_dicts[dispose_intelligence][::]#防止修改原有列表
		config_calculating.release()
		return cut
	config_calculating.release()
	
	content = getContent(filepath)
	if not content:
		print_safe("{0} Dispose: Unrecognizable file \"{1}\". ".format(state_symbols[-1], filepath))
		return []
	
	if any_clears["space"].get():#删除空格、缩进、回车和换行
		content = content.replace(" ", clear_to).replace("\t", clear_to).replace("\r", clear_to).replace("\n", clear_to)
	if any_clears["digits"].get():#删除数字
		for i in "0123456789%.０１２３４５６７８９●〇壹贰叁肆伍陆柒捌玖拾佰仟":
			content = content.replace(i, clear_to)
	if content is None:
		return []
	
	if 0 == config_modes["mode"]:#精确模式
		cut = list(jieba.cut(content))
	elif 1 == config_modes["mode"]:#全模式
		cut = list(jieba.cut(content, cut_all = True))
	elif 2 == config_modes["mode"]:#搜索引擎模式
		cut = list(jieba.cut_for_search(content))
	elif 3 == config_modes["mode"]:# Paddle 模式
		cut = list(jieba.lcut(content, use_paddle = True))
	else:#指定了错误的模式
		return []
	
	if any_clears["stopwords"].get():#清除停用词
		for i in range(len(cut) - 1, -1, -1):#从后往前清除
			if cut[i] in config_stopwords:
				del cut[i]
	
	print_safe("{0} {1}".format(state_symbols[None], cut))
	config_calculating.acquire()
	if not do_not_store:
		config_calculated_dicts[dispose_intelligence] = cut
	config_calculating.release()
	return cut

def walk_folder():
	config_filepaths = []
	for (root, dirs, files) in os.walk(config_paths["data"]):
		for file in files:
			config_filepaths.append(os.path.join(root, file))
	return config_filepaths

def clear(targets):#清除结果数据
	lists = [os.path.join(config_modes["output"], target) for target in {"Splitter":splitter_paths, "Similarity":similarity_paths, "Sentiment":sentiment_paths}[targets].values()]
	if MessageBox("\n{0} ".format(state_symbols[None]).join(["This will remove all the previous related results listed as follows. "] + lists), 0):
		print_safe("{0} Clear: Trying to remove related results about \"{1}\", please wait. ".format(state_symbols[0], targets))
		clear_target_tmp = True
		for target in lists:
			if os.path.exists(target):
				try:
					rmtree(target) if os.path.isdir(target) else os.remove(target)
					print_safe("{0} Clear: Successfully remove \"{1}\". ".format(state_symbols[None], target))
				except Exception as remove_exception:
					clear_target_tmp = False
					print_safe("{0} Clear: Error removing \"{1}\" since {2}. ".format(state_symbols[None], target, remove_exception))
			else:
				print_safe("{0} Clear: \"{1}\" doesn\'t exist. ".format(state_symbols[None], target))
		if clear_target_tmp:
			if os.path.isdir(config_modes["output"]):#输出文件夹存在
				if len(os.listdir(config_modes["output"])) > 0:#还有其它输出结果
					MessageBox("All the previous related results are removed. ", 1)
				elif MessageBox("The output folder is empty, would you like to remove it?", 0):
					try:
						os.removedirs(config_modes["output"])#可以防止删除非空文件夹
						MessageBox("The empty output folder is removed. ", 1)
					except Exception as remove_exception:
						print_safe("{0} Clear: Error removing the empty output folder since {1}. ".format(state_symbols[None], remove_exception))
						MessageBox("Can not remove the empty output folder. ", -1)
		elif MessageBox("Some previous related results could not be removed. \n{0} Please make sure they are not opened. \n{0} Press \"OK\" to run as administrator if necessary. ".format(state_symbols[None]), 0):
			ElevatePrivileges()

def common_sorted(common_filepaths, common_sorted_config):#排序
	if 0 <= common_sorted_config <= 3:
		return sorted(										\
			common_filepaths, 									\
			key = lambda x:{									\
				0:x, 				#文件名					\
				1:os.path.splitext(x)[0].lower(), 		#不区分大小写按字母			\
				2:splitextdate(x)[0].lower(), 		#获取文件来源且不区分大小写		\
				3:float(splitextdate(x)[1])		#时间					\
			}[common_sorted_config]								\
		)
	else:
		return common_filepaths

def common_generate_dicts(cut):#生成字典
	common_dicts = {}
	for word in set(cut):
		if word not in common_dicts:#加速运行
			common_dicts[word] = cut.count(word)
	return common_dicts

def result_output_txtfile(filepath, cut, prompt, encoding = "utf-8"):#输出 txt 结果
	try:
		with open(filepath, "w", encoding = encoding) as f:
			f.write("\n".join(cut))
		print_safe("{0} {1}: Finish writing \"{2}\". ".format(state_symbols[1], prompt, filepath))
		return True
	except Exception as txt_output_exception_1:
		try:
			result_output_folder = os.path.split(filepath)[0]
			if os.path.isdir(result_output_folder):#文件夹存在
				print_safe("{0} {1}: Error writing \"{2}\" since {3}. ".format(state_symbols[-1], prompt, filepath, txt_output_exception_1))
				return False
			else:
				print_safe("{0} {1}: Error writing \"{2}\", try making folders. ".format(state_symbols[None], prompt, filepath))
				os.makedirs(result_output_folder)
				with open(filepath, "w", encoding = encoding) as f:
					f.write("\n".join(cut))
				print_safe("{0} {1}: Finish writing \"{2}\". ".format(state_symbols[1], prompt, filepath))
				return True
		except Exception as txt_output_exception_2:
			print_safe("{0} {1}: Error writing \"{2}\" since {3}. ".format(state_symbols[-1], prompt, filepath, txt_output_exception_2))
			return False

def result_output_csvexcel(filepath, pf, prompt, index = False):#输出 csvexcel 结果
	try:
		{".csv":pf.to_csv, ".xls":pf.to_excel, ".xlsx":pf.to_excel}[os.path.splitext(filepath)[1].lower()](filepath, index = index)
		print_safe("{0} {1}: Finish writing \"{2}\". ".format(state_symbols[1], prompt, filepath))
		return True
	except Exception as csvexcel_output_exception_1:
		try:
			result_output_folder = os.path.split(filepath)[0]
			if os.path.isdir(result_output_folder):#文件夹存在
				print_safe("{0} {1}: Error writing \"{2}\" since {3}. ".format(state_symbols[-1], prompt, filepath, csvexcel_output_exception_1))
				return False
			else:
				print_safe("{0} {1}: Error writing \"{2}\", try making folders. ".format(state_symbols[None], prompt, filepath))
				os.makedirs(result_output_folder)
				{".csv":pf.to_csv, ".xls":pf.to_excel, ".xlsx":pf.to_excel}[os.path.splitext(filepath)[1].lower()](filepath, index = index)
				print_safe("{0} {1}: Finish writing \"{2}\". ".format(state_symbols[1], prompt, filepath))
				return True
		except Exception as csvexcel_output_exception_2:
			print_safe("{0} {1}: Error writing \"{2}\" since {3}. ".format(state_symbols[-1], prompt, filepath, csvexcel_output_exception_2))
			return False


# Splitter 子函数
def splitter_ety_change_file(event):# Splitter 输出文件路径检查函数
	reset_default_path = "splitter.csv"
	rollback = splitter_paths["file"]
	splitter_paths["file"] = splitter_sv_file.get()
	if rollback != splitter_paths["file"]:#作出了修改
		i, j = 0, len(splitter_paths["file"]) - 1
		if j < 0: splitter_paths["file"] = reset_default_path#空串
		while splitter_paths["file"][i] == " " and i < j: i += 1#定位到前面的第一个非空格字符
		while splitter_paths["file"][j] == " " and j > 0: j -= 1#定位到后面的最后一个非空格字符
		splitter_paths["file"] = splitter_paths["file"][i:j + 1]#截取片段
		reset_default_flag = False
		if not splitter_paths["file"]:#去除头尾空格后空串
			splitter_paths["file"] = reset_default_path
			reset_default_flag = True
		if splitter_chkdir():
			splitter_sv_file.set(splitter_paths["file"])
			print_safe("{0} Splitter: Path of \"file\" has been {1} \"{2}\". ".format(state_symbols[1], "reset to default folder" if reset_default_flag else "changed to", splitter_paths["file"]))
		else:
			splitter_paths["file"] = rollback
			MessageBox("Folders of data, sample, and output should be different with each others. Special characters are not allowed. ", -1)
			splitter_sv_file.set(rollback)# 回滚文字

def splitter_ety_change_folder(event):# Splitter 输出目录路径检查函数
	reset_default_path = "splitter"
	rollback = splitter_paths["folder"]
	splitter_paths["folder"] = splitter_sv_folder.get()
	if rollback != splitter_paths["folder"]:#作出了修改
		i, j = 0, len(splitter_paths["folder"]) - 1
		if j < 0: splitter_paths["folder"] = reset_default_path#空串
		while splitter_paths["folder"][i] == " " and i < j: i += 1#定位到前面的第一个非空格字符
		while splitter_paths["folder"][j] == " " and j > 0: j -= 1#定位到后面的最后一个非空格字符
		splitter_paths["folder"] = splitter_paths["folder"][i:j + 1]#截取片段
		reset_default_flag = False
		if not splitter_paths["folder"]:#去除头尾空格后空串
			splitter_paths["folder"] = reset_default_path
			reset_default_flag = True
		if splitter_chkdir():
			splitter_sv_folder.set(splitter_paths["folder"])
			print_safe("{0} Splitter: Path of \"folder\" has been {1} \"{2}\". ".format(state_symbols[1], "reset to default folder" if reset_default_flag else "changed to", splitter_paths["folder"]))
		else:
			splitter_paths["folder"] = rollback
			MessageBox("Folders of data, sample, and output should be different with each others. Special characters are not allowed. ", -1)
			splitter_sv_folder.set(rollback)# 回滚文字

def splitter_ety_change_wordcloud(event):# Splitter 输出词云路径检查函数
	reset_default_path = "wordcloud.png"
	rollback = splitter_paths["wordcloud"]
	splitter_paths["wordcloud"] = splitter_sv_wordcloud.get()
	if rollback != splitter_paths["wordcloud"]:#作出了修改
		i, j = 0, len(splitter_paths["wordcloud"]) - 1
		if j < 0: splitter_paths["wordcloud"] = reset_default_path#空串
		while splitter_paths["wordcloud"][i] == " " and i < j: i += 1#定位到前面的第一个非空格字符
		while splitter_paths["wordcloud"][j] == " " and j > 0: j -= 1#定位到后面的最后一个非空格字符
		splitter_paths["wordcloud"] = splitter_paths["wordcloud"][i:j + 1]#截取片段
		reset_default_flag = False
		if not splitter_paths["wordcloud"]:#去除头尾空格后空串
			splitter_paths["wordcloud"] = reset_default_path
			reset_default_flag = True
		if splitter_chkdir():
			splitter_sv_wordcloud.set(splitter_paths["wordcloud"])
			print_safe("{0} Splitter: Path of \"wordcloud\" has been {1} \"{2}\". ".format(state_symbols[1], "reset to default folder" if reset_default_flag else "changed to", splitter_paths["wordcloud"]))
		else:
			splitter_paths["wordcloud"] = rollback
			MessageBox("Folders of data, sample, and output should be different with each others. Special characters are not allowed. ", -1)
			splitter_sv_wordcloud.set(rollback)# 回滚文字

def splitter_lock():
	if splitter_btn_lock["fg"] == state_fg[0]:#未上锁则上锁
		for controller in splitter_controllers:#群控禁用
			controller["state"] = DISABLED
		config_lock_set(False)
		splitter_btn_lock["fg"] = state_fg[1]
		splitter_btn_lock["text"] = "Lock: On"
		splitter_btn_clear["state"] = NORMAL#解锁清除按钮
		splitter_btn_run["state"] = NORMAL#解锁运行按钮
	else:#已上锁则解锁
		for controller in splitter_controllers:#群控解禁
			controller["state"] = NORMAL
		config_lock_set(True)
		splitter_btn_lock["fg"] = state_fg[0]
		splitter_btn_lock["text"] = "Lock: Off"
		splitter_btn_clear["state"] = DISABLED#禁用清除按钮
		splitter_btn_run["state"] = DISABLED#禁用运行按钮

def splitter_lockset(state):#锁定或解锁 Splitter 所有按钮
	splitter_btn_lock["state"] = state
	splitter_btn_clear["state"] = state
	splitter_btn_run["state"] = state
	tk.update()

def splitter_check_environment():#检查环境
	if not environment_satisfy():
		MessageBox("Environment check required, please check it initially. ", -1)
		return False
	if not MessageBox("It might take a long while to perform Splitter. \n{0} Note the results would be overwritten if previous ones exist. \n{0} It may look stuck while drawing after finishing the progress. \n{0} Please press \"OK\" to continue. ".format(state_symbols[None]), 0):
		return False
	splitter_result_folder = os.path.join(config_modes["output"], splitter_paths["folder"])
	if not os.path.isdir(splitter_result_folder):#保存结果的文件夹不存在
		print_safe("{0} Splitter: The result folder \"{1}\" doesn\'t exist. Making directories, please wait. ".format(state_symbols[0], splitter_result_folder))
		try:
			os.makedirs(splitter_result_folder)
			print_safe("{0} Splitter: The result folder \"{1}\" has been successfully made. ".format(state_symbols[1], splitter_result_folder))
		except Exception as splitter_makedirs_exception:
			print_safe("{0} Splitter: Error making \"{1}\" since {2}. ".format(state_symbols[-1], splitter_result_folder, splitter_makedirs_exception))
			if WinOS:# Windows 操作系统
				if UAC:#拥有 UAC
					if MessageBox("Splitter operation has been aborted. Consider clearing results and try again. \n{0} If that do not work, you might need to run as administrator. \n{0} Press \"OK\" to run as administrator if not now. ".format(state_symbols[None]), 0):
						ElevatePrivileges()
				else:
					MessageBox("Splitter operation has been aborted. Consider clearing results and try again. ", -1)
			else:
				if MessageBox("Splitter operation has been aborted. Consider clearing results and try again. \n{0} If that do not work, you might need to run as super user. \n{0} Press \"OK\" to run with sudo if \"sudo\" is supported. ".format(state_symbols[None]), 0):
					ElevatePrivileges()
			return False
	return True

def splitter_calc_frequency(splitter_tmp_lists, virtual_total_cnt = None):#计算词频
	word_total_cnt = sum([tp[1] for tp in splitter_tmp_lists]) if virtual_total_cnt is None else virtual_total_cnt#如果没有预先计算总数则进行计算
	if word_total_cnt > 0:#合法总数
		for i in range(len(splitter_tmp_lists)):
			splitter_tmp_lists[i] += (splitter_tmp_lists[i][1] / word_total_cnt, )
	else:#非法总数
		for i in range(len(splitter_tmp_lists)):
			splitter_tmp_lists[i] += (nan, )
	return splitter_tmp_lists

def splitter_output_bridge(splitter_any_dict, splitter_any_filepath):#连接字典和生成文件的大桥
	splitter_ori_tuple = splitter_calc_frequency(list(splitter_any_dict.items()))
	splitter_sorted_tuple = sorted(splitter_ori_tuple, key = lambda x:x[1], reverse = True)#建议用 x:x[1] 而非 x:x[2] 因为 x[2] 可能会出现 nan
	splitter_result_length = len(splitter_ori_tuple)
	return result_output_csvexcel(											#输出 csvexcel 数据				\
		splitter_any_filepath, 										#输出文件路径				\
		DF(												#将二维列表转为 DataFrame 格式		\
			array(											#使用 numpy 的列表执行			\
				[[i for i in range(1, splitter_result_length + 1)]]						#输出索引				\
				+ array(splitter_ori_tuple).T.tolist()							#原始排序（先出现的词优先）		\
				+ array([("", j) for j in range(1, splitter_result_length + 1)]).T.tolist()				#输出间隔和索引				\
				+ array(splitter_sorted_tuple).T.tolist()							#频率排序（出现越多越优先）		\
			).T.tolist(), 										#转回原二维列表				\
			columns = ["Original", "Word", "Count", "Frequency"] + [""] + ["Sorted", "Word", "Count", "Frequency"]		#表头					\
		), 																	\
		"Splitter"																	\
	)

def splitter_draw_wordcloud(splitter_any_tuple):#绘制词云
	print_safe("{0} Splitter: Begin to generate the wordcloud, please wait. ".format(state_symbols[0]))
	splitter_wordcloud_text = " ".join([" ".join([item[0]] * item[1]) for item in splitter_any_tuple])
	wordcloud = WordCloud(width = splitter_draw_configs["width"], height = splitter_draw_configs["height"], font_path = config_paths["ttf"], background_color = splitter_draw_configs["background_color"], collocations = False).generate(splitter_wordcloud_text)
	use("Agg")#防止 plt.close() 关闭 mainloop
	plt.imshow(wordcloud, interpolation = "bilinear")
	plt.axis("off")
	plt.rcParams["figure.dpi"] = splitter_draw_configs["width"] + splitter_draw_configs["height"]
	#plt.show()
	plt.rcParams["savefig.dpi"] = splitter_draw_configs["width"] + splitter_draw_configs["height"]
	plt.savefig(os.path.join(config_modes["output"], splitter_paths["wordcloud"]))
	plt.close()

def splitter_walk_folder():#遍历文件并处理
	print_safe("{0} Splitter: Processing, please wait. ".format(state_symbols[0]))
	splitter_filepaths = walk_folder()
	if len(splitter_filepaths) <= 0:
		MessageBox("Splitter aborted as no input data found. ", -1)
		return False
	print_safe(splitter_filepaths)
	print_safe("{0} Splitter: Successfully gather {1} data. ".format(state_symbols[1], len(splitter_filepaths)))
	splitter_progresstext["fg"] = state_fg[0]#进度复原
	splitter_progressbar["value"] = 0
	splitter_progressbar["maximum"] = len(splitter_filepaths)#考虑总样本
	splitter_progressnum["text"] = "Progress: 0.00%"
	tk.update()
	splitter_output_flag = True
	splitter_array_dicts = {}
	for filepath in splitter_filepaths:
		print_safe("{0} Splitter: {1}".format(state_symbols[0], filepath))
		_cut = dispose(filepath, splitter_clears)
		_cut_length = len(_cut)
		for i in splitter_gram_N:
			cut = ["".join([_cut[j + k] for k in range(i)]) for j in range(_cut_length - i)]
			result_output_txtfile(os.path.join(config_modes["output"], os.path.join(splitter_paths["folder"], str(i))) + os.path.splitext(filepath[len(config_paths["data"]):])[0] + ".txt", cut, "Splitter")
			splitter_dicts = common_generate_dicts(cut)
			splitter_output_flag = splitter_output_bridge(											\
				splitter_dicts, 							#字典						\
				(								#路径开始					\
					os.path.join(												\
						config_modes["output"], 						#输出文件夹			\
						os.path.join(splitter_paths["folder"], str(i))					#分文件夹			\
					)								#取目标目录路径				\
					+ os.path.splitext(filepath[len(config_paths["data"]):])[0]			#取原有目录结构				\
					+ os.path.splitext(splitter_paths["file"])[1]					#取总输出 csvexcel 文件的拓展名		\
				)								#路径结尾					\
			) and splitter_output_flag# splitter_output_flag 要放在后面
			for splitter_key in list(splitter_dicts.keys()):
				splitter_array_dicts.setdefault(i, {})
				splitter_array_dicts[i].setdefault(splitter_key, 0)
				splitter_array_dicts[i][splitter_key] += splitter_dicts[splitter_key]
		splitter_progressbar["value"] += 1
		splitter_progressnum["text"] = "Progress: {0:.2f}%".format(100 * splitter_progressbar["value"] / splitter_progressbar["maximum"])
		splitter_progresstext["text"] = "{0} / {1}".format(splitter_progressbar["value"], splitter_progressbar["maximum"])
		tk.update()
	else:#总的
		splitter_output_flag = splitter_output_bridge(splitter_array_dicts[1], os.path.join(config_modes["output"], splitter_paths["file"])) and splitter_output_flag
		splitter_draw_wordcloud(tuple(splitter_array_dicts[1].items()))
		if not splitter_output_flag:
			raise OSError("some files could not be written")
		splitter_progresstext["fg"] = state_fg[1]#所有操作成功完成
		tk.update()#更新 UI
	return True
			
def splitter_main():# Splitter 主函数
	while True:
		thread_splitter_lock.acquire()
		if environment_satisfy() is None:#说明需要回收线程了
			break
		splitter_lockset(DISABLED)
		thread_splitter_lock.release()#设置为正在运行
		try:
			if splitter_check_environment() and config_load_userdict("Splitter") and splitter_walk_folder():#使用短路逻辑与控制串联流程
				MessageBox("(^_^) Splitter finished successfully. ", 1)
			else:
				print_safe("{0} Splitter: Splitter aborted. ".format(state_symbols[-1]))
		except Exception as splitter_exception:
			try:
				plt.close()#防止生成过程发生异常导致 plt 未被关闭
			except:
				pass
			if environment_satisfy() is None:#线程被迫中止
				break
			splitter_progresstext["fg"] = state_fg[-1]#进度出错
			tk.update()
			MessageBox(")-: Splitter has some problems and aborted. ", -1)
			print_safe("{0} Splitter: Splitter aborted since {1}. ".format(state_symbols[-1], ("\"{0}\"" if str(splitter_exception)[-1] in (" ", "\t") else "\"{0} \"").format(str(splitter_exception).replace("\r", "\\r").replace("\n","\\n").replace("\\", "\\\\").replace("\"", "\\\"")) if str(splitter_exception).replace(" ", "")[-1] in ",;.!" else splitter_exception))
		thread_splitter_lock.acquire()#重新上锁
		splitter_lockset(NORMAL)


# Similarity 子函数
def similarity_ety_change_file(event):# Similarity 输出文件路径检查函数
	reset_default_path = "similarity.csv"
	rollback = similarity_paths["file"]
	similarity_paths["file"] = similarity_sv_file.get()
	if rollback != similarity_paths["file"]:#作出了修改
		i, j = 0, len(similarity_paths["file"]) - 1
		if j < 0: similarity_paths["file"] = reset_default_path#空串
		while similarity_paths["file"][i] == " " and i < j: i += 1#定位到前面的第一个非空格字符
		while similarity_paths["file"][j] == " " and j > 0: j -= 1#定位到后面的最后一个非空格字符
		similarity_paths["file"] = similarity_paths["file"][i:j + 1]#截取片段
		reset_default_flag = False
		if not similarity_paths["file"]:#去除头尾空格后空串
			similarity_paths["file"] = reset_default_path
			reset_default_flag = True
		if similarity_chkdir():
			similarity_sv_file.set(similarity_paths["file"])
			print_safe("{0} Similarity: Path of \"file\" has been {1} \"{2}\". ".format(state_symbols[1], "reset to default folder" if reset_default_flag else "changed to", similarity_paths["file"]))
		else:
			similarity_paths["file"] = rollback
			MessageBox("Folders of data, sample, and output should be different with each others. Special characters are not allowed. ", -1)
			similarity_sv_file.set(rollback)# 回滚文字

def similarity_ety_change_folder(event):# Similarity 输出目录路径检查函数
	reset_default_path = "similarity"
	rollback = similarity_paths["folder"]
	similarity_paths["folder"] = similarity_sv_folder.get()
	if rollback != similarity_paths["folder"]:#作出了修改
		i, j = 0, len(similarity_paths["folder"]) - 1
		if j < 0: similarity_paths["folder"] = reset_default_path#空串
		while similarity_paths["folder"][i] == " " and i < j: i += 1#定位到前面的第一个非空格字符
		while similarity_paths["folder"][j] == " " and j > 0: j -= 1#定位到后面的最后一个非空格字符
		similarity_paths["folder"] = similarity_paths["folder"][i:j + 1]#截取片段
		reset_default_flag = False
		if not similarity_paths["folder"]:#去除头尾空格后空串
			similarity_paths["folder"] = reset_default_path
			reset_default_flag = True
		if similarity_chkdir():
			similarity_sv_folder.set(similarity_paths["folder"])
			print_safe("{0} Similarity: Path of \"folder\" has been {1} \"{2}\". ".format(state_symbols[1], "reset to default folder" if reset_default_flag else "changed to", similarity_paths["folder"]))
		else:
			similarity_paths["folder"] = rollback
			MessageBox("Folders of data, sample, and output should be different with each others. Special characters are not allowed. ", -1)
			similarity_sv_folder.set(rollback)# 回滚文字

def set_similarity_order(event):
	if similarity_configs["order"] != int(similarity_order_sv.get()[0]):
		similarity_configs["order"] = int(similarity_order_sv.get()[0])
		print_safe("{0} Similarity: Similarity order has been changed to \"{1}\". ".format(state_symbols[1], similarity_values[similarity_configs["order"]]))

def similarity_lock():
	if similarity_btn_lock["fg"] == state_fg[0]:#未上锁则上锁
		for controller in similarity_controllers:#群控禁用
			controller["state"] = DISABLED
		similarity_combobox["state"] = DISABLED#禁用自家 Combobox
		config_lock_set(False)
		similarity_btn_lock["fg"] = state_fg[1]
		similarity_btn_lock["text"] = "Lock: On"
		similarity_btn_clear["state"] = NORMAL#解锁清除按钮
		similarity_btn_run["state"] = NORMAL#解锁运行按钮
	else:#已上锁则解锁
		for controller in similarity_controllers:#群控解禁
			controller["state"] = NORMAL
		similarity_combobox["state"] = "readonly"#启用自家 Combobox
		config_lock_set(True)
		similarity_btn_lock["fg"] = state_fg[0]
		similarity_btn_lock["text"] = "Lock: Off"
		similarity_btn_clear["state"] = DISABLED#禁用清除按钮
		similarity_btn_run["state"] = DISABLED#禁用运行按钮

def similarity_lockset(state):#锁定或解锁 Similarity 所有按钮
	similarity_btn_lock["state"] = state
	similarity_btn_clear["state"] = state
	similarity_btn_run["state"] = state
	tk.update()

def similarity_check_environment():#检查环境
	if not environment_satisfy():
		MessageBox("Environment check required, please check it initially. ", -1)
		return False
	if not MessageBox("It might take a while to perform Similarity, especially when it initials. \n{0} Note the results would be overwritten if previous ones exist. \n{0} Generation intelligence would be on to fasten the process. \n{0} Please press \"OK\" to continue. ".format(state_symbols[None]), 0):
		return False
	similarity_result_folder = os.path.join(config_modes["output"], similarity_paths["folder"])
	if not os.path.isdir(similarity_result_folder):#保存结果的文件夹不存在
		print_safe("{0} Similarity: The result folder \"{1}\" doesn\'t exist. Making directories, please wait. ".format(state_symbols[0], similarity_result_folder))
		try:
			os.makedirs(similarity_result_folder)
			print_safe("{0} Similarity: The result folder \"{1}\" has been successfully made. ".format(state_symbols[1], similarity_result_folder))
		except Exception as similarity_makedirs_exception:
			print_safe("{0} Similarity: Error making \"{1}\" since {2}. ".format(state_symbols[-1], similarity_result_folder, similarity_makedirs_exception))
			if WinOS:# Windows 操作系统
				if UAC:#拥有 UAC
					if MessageBox("Similarity operation has been aborted. Consider clearing results and try again. \n{0} If that do not work, you might need to run as administrator. \n{0} Press \"OK\" to run as administrator if not now. ".format(state_symbols[None]), 0):
						ElevatePrivileges()
				else:
					MessageBox("Similarity operation has been aborted. Consider clearing results and try again. ", -1)
			else:
				if MessageBox("Similarity operation has been aborted. Consider clearing results and try again. \n{0} If that do not work, you might need to run as super user. \n{0} Press \"OK\" to run with sudo if \"sudo\" is supported. ".format(state_symbols[None]), 0):
					ElevatePrivileges()
			return False
	return True

def splitextdate(filepath):#分离文件和日期
	pure_filename = os.path.splitext(os.path.split(filepath)[1])[0]
	re_lists = findall("\\d{8}(?=\\d*)", pure_filename)#匹配出所有八位数字
	if len(re_lists) > 0:#文件名中含有日期
		pure_filename_lists = pure_filename.split(re_lists[-1])
		return re_lists[-1].join(pure_filename_lists[:-1]) + pure_filename_lists[-1], re_lists[-1]
	else:#文件名中不含有日期
		try:
			return pure_filename, strftime("%Y%m%d", localtime(os.stat(full_path).st_mtime))#返回文件修改日期
		except:
			return pure_filename, "inf"#文件修改日期不可用则使用正无穷（排序时会排到最后面去）

def zip_gram(embeddings, gram):#压缩 embeddings
	if gram is not None and gram > 0:
		embeddings = list(zip(*[embeddings[i:] for i in range(gram)]))
		for i in range(len(embeddings)):
			embeddings[i] = similarity_configs["splitter"].join(embeddings[i])
	return embeddings

def make_idf_dicts(similarity_filepaths, gram):
	similarity_idf.clear()
	for filepath in similarity_filepaths:
		embeddings = dispose(filepath, similarity_clears)
		embeddings = set(zip_gram(embeddings, gram))
		for ebd in embeddings:
			similarity_idf.setdefault(ebd, 0)
			similarity_idf[ebd] += 1

def get_embeddings(filepath, gram):#计算 embeddings
	embeddings = dispose(filepath, similarity_clears)
	embeddings = zip_gram(embeddings, gram)
	dicts = common_generate_dicts(embeddings)
	total_value = len(embeddings)#总数即列表总长度
	for i in list(dicts.keys()):#计算词频
		dicts[i] /= total_value
	return dicts

def get_cos_similarity(vector_1, vector_2):#计算两个向量的余弦值
	vec_dim_1, vec_dim_2 = len(vector_1), len(vector_2)
	assert(vec_dim_1 == vec_dim_2)#两者长度要一致
	vec_dim = vec_dim_1
	numerator = 0
	for i in range(vec_dim):
		numerator += vector_1[i] * vector_2[i]
	sq_1, sq_2 = 0, 0
	for i in range(vec_dim):#求模
		sq_1 += vector_1[i] * vector_1[i]
		sq_2 += vector_2[i] * vector_2[i]
	denominator = sq_1 ** (1 / 2) * sq_2 ** (1 / 2)#分母
	return 1 if denominator == 0 else float(numerator) / denominator#如果分母为 0 返回 1 否则返回余弦值

def get_similarity_value(filepath_1, filepath_2, gram, similarity_all_cnt):#计算两个文件在某个 gram 下的相似度
	global similarity_embeddings_1, similarity_embeddings_2
	similarity_embeddings_1 = get_embeddings(filepath_1, gram) if similarity_embeddings_1 is None else similarity_embeddings_1#没计算的时候才执行计算
	similarity_embeddings_2 = get_embeddings(filepath_2, gram)#第二个永远处于未计算的状态
	sum_embeddings_1, sum_embeddings_2 = sum(list(similarity_embeddings_1.values())), sum(list(similarity_embeddings_2.values()))
	if 0 == sum_embeddings_1 or 0 == sum_embeddings_2:#分母为 0 返回 1
		return 1
	embeddings = set(similarity_embeddings_1.keys())
	embeddings.update(set(similarity_embeddings_2.keys()))#整合 embeddings（取并集）
	similarity_vector_1, similarity_vector_2 = [], []
	for ebd in embeddings:#保证对应
		idf = log(similarity_all_cnt / (max(similarity_idf[ebd] if ebd in similarity_idf else 1, 1)))
		similarity_vector_1.append(similarity_embeddings_1[ebd] / sum_embeddings_1 * idf if ebd in similarity_embeddings_1 else 0)
		similarity_vector_2.append(similarity_embeddings_2[ebd] / sum_embeddings_2 * idf if ebd in similarity_embeddings_2 else 0)
	similarity_embeddings_1, similarity_embeddings_2 = similarity_embeddings_2, None
	return get_cos_similarity(similarity_vector_1, similarity_vector_2)

def similarity_output_bridge(similarity_array_lists):#补全至矩形并返回 DF 转置类型
	similarity_max_length = max([len(similarity_single_list) for similarity_single_list in similarity_array_lists])
	for i in range(len(similarity_array_lists)):
		similarity_array_lists[i] += [""] * (similarity_max_length - len(similarity_array_lists[i]))#补全缺失值
	return array(similarity_array_lists).T

def similarity_walk_folder():#遍历文件并处理
	print_safe("{0} Similarity: Processing, please wait. ".format(state_symbols[0]))
	similarity_filepaths = walk_folder()
	if len(similarity_filepaths) < 2:
		MessageBox("Similarity aborted as less than two input data found. ", -1)
		return False
	similarity_filepaths = common_sorted(similarity_filepaths, similarity_configs["order"])
	similarity_filepath_length = len(similarity_filepaths) - 1#考虑总样本 - 1
	similarity_gram_length = len(similarity_configs["gram_N"])
	print_safe(similarity_filepaths)
	print_safe("{0} Similarity: Successfully gather {1} data. ".format(state_symbols[1], similarity_filepath_length))
	similarity_progresstext_main["fg"] = state_fg[0]#主进度复原
	similarity_progressbar_main["value"] = 0
	similarity_progressbar_main["maximum"] = similarity_gram_length * similarity_filepath_length
	similarity_progressnum_main["text"] = "Main: 0.00%"
	similarity_progresstext_sub["fg"] = state_fg[0]#因过程中的短暂完成不考虑变色（短暂完成的短暂变色肉眼看不出来）而直接复原子进度颜色
	tk.update()
	similarity_output_flag = True
	similarity_empty_lists = [[""] * similarity_filepath_length]
	similarity_array_lists = []
	for gcnt, gram in enumerate(set(similarity_configs["gram_N"])):
		similarity_progressbar_sub["value"] = 0
		similarity_progressbar_sub["maximum"] = similarity_filepath_length
		similarity_progressnum_sub["text"] = "Sub: 0.00%"
		similarity_results = []
		make_idf_dicts(similarity_filepaths, gram)#初始化 idf
		for i in range(1, similarity_filepath_length + 1):
			filepath_1, filepath_2 = similarity_filepaths[i - 1], similarity_filepaths[i]
			if (											\
				(0 == similarity_configs["order"] and os.path.split(filepath_1)[0] != os.path.split(filepath_2)[0])		\
				or (2 == similarity_configs["order"] and splitextdate(filepath_1)[0] != splitextdate(filepath_2)[0])		\
			):#部分排序方法需要区分分类
				similarity_results.append([""] * 5)
				print_safe("{0} Similarity: Successfully print delims. ".format(state_symbols[1]))
			else:
				print_safe("{0} Similarity: get_similarity_value(\"{1}\", \"{2}\", {3})".format(state_symbols[None], filepath_1, filepath_2, gram))
				similarity_tmp = get_similarity_value(filepath_1, filepath_2, gram, similarity_filepath_length + 1)
				similarity_results.append([i, filepath_1, filepath_2, gram, similarity_tmp])
				print_safe("{0} Similarity: {1}".format(state_symbols[1], similarity_tmp))
			similarity_progressbar_sub["value"] += 1#子进度条
			similarity_progressnum_sub["text"] = "Sub: {0:.2f}%".format(100 * similarity_progressbar_sub["value"] / similarity_progressbar_sub["maximum"])
			similarity_progresstext_sub["text"] = "{0} / {1}".format(similarity_progressbar_sub["value"], similarity_progressbar_sub["maximum"])
			similarity_progressbar_main["value"] += 1#主进度条
			similarity_progressnum_main["text"] = "Main: {0:.2f}%".format(100 * similarity_progressbar_main["value"] / similarity_progressbar_main["maximum"])
			tk.update()	
		similarity_output_flag = result_output_csvexcel(												\
			(															\
				os.path.join(								#路径开始				\
					os.path.join(config_modes["output"], similarity_paths["folder"]), 			#取目标目录路径			\
					"gram_{0}{1}".format(gram, os.path.splitext(similarity_paths["file"])[1])			# csvexcel 文件的全文件名		\
				)									#路径结尾				\
			), 															\
			DF(															\
				similarity_results, 													\
				columns = ["index", "Filepath_1", "Filepath_2", "Gram", "Similarity"]								\
			), 															\
			"Similarity"														\
		) and similarity_output_flag# similarity_output_flag 要放在后面
		similarity_array_lists += array(similarity_results).T.tolist()
		similarity_array_lists += similarity_empty_lists
		similarity_progresstext_main["text"] = "{0} / {1}".format(gcnt + 1, similarity_gram_length)
		tk.update()
	else:#总的
		similarity_array_lists = similarity_output_bridge(similarity_array_lists[:-1])#去掉最后一行空行并补全至矩形
		similarity_output_flag = result_output_csvexcel(										#输出 csvexcel 数据				\
			os.path.join(config_modes["output"], similarity_paths["file"]), 								#输出文件路径				\
			DF(																		\
				similarity_array_lists, 															\
				columns = (["index", "Filepath_1", "Filepath_2", "Gram", "Similarity", ""] * len(similarity_configs["gram_N"]))[:-1]		#去掉循环生成后最后一个多余的列		\
			), 																		\
			"Similarity"																	\
		) and similarity_output_flag
		if not similarity_output_flag:
			raise OSError("some files could not be written")
		similarity_progresstext_sub["fg"] = state_fg[1]#子进度最后一次短暂完成（非最后一次短暂完成过程不更改）
		similarity_progresstext_main["fg"] = state_fg[1]#所有操作成功完成
		tk.update()#更新 UI
	return True

def similarity_main():# Similarity 主函数
	while True:
		thread_similarity_lock.acquire()
		if environment_satisfy() is None:#说明需要回收线程了
			break
		similarity_lockset(DISABLED)
		thread_similarity_lock.release()#设置为正在运行
		try:
			if similarity_check_environment() and config_load_userdict("Similarity") and similarity_walk_folder():#使用短路逻辑与控制串联流程
				MessageBox("(^_^) Similarity finished successfully. ", 1)
			else:
				print_safe("{0} Similarity: Similarity aborted. ".format(state_symbols[-1]))
		except Exception as similarity_exception:#进度出错
			if environment_satisfy() is None:#线程被迫中止
				break
			similarity_progresstext_sub["fg"] = state_fg[-1]#更改子进度颜色
			similarity_progresstext_main["fg"] = state_fg[-1]#更改主进度颜色
			tk.update()
			MessageBox(")-: Similarity has some problems and aborted. ", -1)
			print_safe("{0} Similarity: Similarity aborted since {1}. ".format(state_symbols[-1], ("\"{0}\"" if str(similarity_exception)[-1] in (" ", "\t") else "\"{0} \"").format(str(similarity_exception).replace("\r", "\\r").replace("\n","\\n").replace("\\", "\\\\").replace("\"", "\\\"")) if str(similarity_exception).replace(" ", "")[-1] in ",;.!" else similarity_exception))
		thread_similarity_lock.acquire()#重新上锁
		similarity_lockset(NORMAL)


# Sentiment 子函数
def sentiment_ety_change_file(event):# Sentiment 输出文件路径检查函数
	reset_default_path = "sentiment.csv"
	rollback = sentiment_paths["file"]
	sentiment_paths["file"] = sentiment_sv_file.get()
	if rollback != sentiment_paths["file"]:#作出了修改
		i, j = 0, len(sentiment_paths["file"]) - 1
		if j < 0: sentiment_paths["file"] = reset_default_path#空串
		while sentiment_paths["file"][i] == " " and i < j: i += 1#定位到前面的第一个非空格字符
		while sentiment_paths["file"][j] == " " and j > 0: j -= 1#定位到后面的最后一个非空格字符
		sentiment_paths["file"] = sentiment_paths["file"][i:j + 1]#截取片段
		reset_default_flag = False
		if not sentiment_paths["file"]:#去除头尾空格后空串
			sentiment_paths["file"] = reset_default_path
			reset_default_flag = True
		if sentiment_chkdir():
			sentiment_sv_file.set(sentiment_paths["file"])
			print_safe("{0} Sentiment: Path of \"file\" has been {1} \"{2}\". ".format(state_symbols[1], "reset to default folder" if reset_default_flag else "changed to", sentiment_paths["file"]))
		else:
			sentiment_paths["file"] = rollback
			MessageBox("Folders of data, sample, and output should be different with each others. Special characters are not allowed. ", -1)
			sentiment_sv_file.set(rollback)# 回滚文字

def sentiment_ety_change_folder(event):# Sentiment 输出目录路径检查函数
	reset_default_path = "sentiment"
	rollback = sentiment_paths["folder"]
	sentiment_paths["folder"] = sentiment_sv_folder.get()
	if rollback != sentiment_paths["folder"]:#作出了修改
		i, j = 0, len(sentiment_paths["folder"]) - 1
		if j < 0: sentiment_paths["folder"] = reset_default_path#空串
		while sentiment_paths["folder"][i] == " " and i < j: i += 1#定位到前面的第一个非空格字符
		while sentiment_paths["folder"][j] == " " and j > 0: j -= 1#定位到后面的最后一个非空格字符
		sentiment_paths["folder"] = sentiment_paths["folder"][i:j + 1]#截取片段
		reset_default_flag = False
		if not sentiment_paths["folder"]:#去除头尾空格后空串
			sentiment_paths["folder"] = reset_default_path
			reset_default_flag = True
		if sentiment_chkdir():
			sentiment_sv_folder.set(sentiment_paths["folder"])
			print_safe("{0} Sentiment: Path of \"folder\" has been {1} \"{2}\". ".format(state_symbols[1], "reset to default folder" if reset_default_flag else "changed to", sentiment_paths["folder"]))
		else:
			sentiment_paths["folder"] = rollback
			MessageBox("Folders of data, sample, and output should be different with each others. Special characters are not allowed. ", -1)
			sentiment_sv_folder.set(rollback)# 回滚文字

def set_sentiment_order(event):
	global sentiment_config
	if sentiment_config != sentiment_order_sv.get():
		sentiment_config = sentiment_order_sv.get()
		print_safe("{0} Sentiment: Sentiment order has been changed to \"{1}\". ".format(state_symbols[1], sentiment_config))

def sentiment_lock():
	if sentiment_btn_lock["fg"] == state_fg[0]:#未上锁则上锁
		for controller in sentiment_controllers:#群控禁用
			controller["state"] = DISABLED
		sentiment_combobox["state"] = DISABLED#禁用自家 Combobox
		config_lock_set(False)
		sentiment_btn_lock["fg"] = state_fg[1]
		sentiment_btn_lock["text"] = "Lock: On"
		sentiment_btn_clear["state"] = NORMAL#解锁清除按钮
		sentiment_btn_run["state"] = NORMAL#解锁运行按钮
	else:#已上锁则解锁
		for controller in sentiment_controllers:#群控解禁
			controller["state"] = NORMAL
		sentiment_combobox["state"] = "readonly"#启用自家 Combobox
		config_lock_set(True)
		sentiment_btn_lock["fg"] = state_fg[0]
		sentiment_btn_lock["text"] = "Lock: Off"
		sentiment_btn_clear["state"] = DISABLED#禁用清除按钮
		sentiment_btn_run["state"] = DISABLED#禁用运行按钮

def sentiment_lockset(state):#锁定或解锁 Sentiment 所有按钮
	sentiment_btn_lock["state"] = state
	sentiment_btn_clear["state"] = state
	sentiment_btn_run["state"] = state
	tk.update()

def sentiment_check_environment():#检查环境
	if not environment_satisfy():
		MessageBox("Environment check required, please check it initially. ", -1)
		return False
	if not MessageBox("It might take a long while to perform Sentiment. \n{0} Note the results would be overwritten if previous ones exist. \n{0} Generation intelligence would be on if you have split before. \n{0} Please press \"OK\" to continue. ".format(state_symbols[None]), 0):
		return False
	sentiment_result_folder = os.path.join(config_modes["output"], sentiment_paths["folder"])
	if not os.path.isdir(sentiment_result_folder):#保存结果的文件夹不存在
		print_safe("{0} Sentiment: The result folder \"{1}\" doesn\'t exist. Making directories, please wait. ".format(state_symbols[0], sentiment_result_folder))
		try:
			os.makedirs(sentiment_result_folder)
			print_safe("{0} Sentiment: The result folder \"{1}\" has been successfully made. ".format(state_symbols[1], sentiment_result_folder))
		except Exception as sentiment_makedirs_exception:
			print_safe("{0} Sentiment: Error making \"{1}\" since {2}. ".format(state_symbols[-1], sentiment_result_folder, sentiment_makedirs_exception))
			if WinOS:# Windows 操作系统
				if UAC:#拥有 UAC
					if MessageBox("Sentiment operation has been aborted. Consider clearing results and try again. \n{0} If that do not work, you might need to run as administrator. \n{0} Press \"OK\" to run as administrator if not now. ".format(state_symbols[None]), 0):
						ElevatePrivileges()
				else:
					MessageBox("Sentiment operation has been aborted. Consider clearing results and try again. ", -1)
			else:
				if MessageBox("Sentiment operation has been aborted. Consider clearing results and try again. \n{0} If that do not work, you might need to run as super user. \n{0} Press \"OK\" to run with sudo if \"sudo\" is supported. ".format(state_symbols[None]), 0):
					ElevatePrivileges()
			return False
	return True

def get_sentiments(content, cut):#计算情感值
	pos_neg = {1:0, -1:0}# 1 为积极，-1 为消极
	len_cnt = len(cut)#存储分词的长度
	if "None" == sentiment_config:#否定词被禁用
		for i in range(len_cnt):
			if cut[i] in config_pos:#积极词汇
				pos_neg[1] += 1
			elif cut[i] in config_neg:#消极词汇
				pos_neg[-1] += 1
	elif "Per Unit" == sentiment_config:#情感单元法
		sentiment_next_not = 1#用于反转计数
		for i in range(len_cnt):#扫描遍历词
			if cut[i] in config_pos:#遇到积极词汇则执行相应的操作并重置 sentiment_next_not
				pos_neg[sentiment_next_not] += 1
				sentiment_next_not = 1
			elif cut[i] in config_neg:#遇到消极词汇则执行相应的操作并重置 sentiment_next_not
				pos_neg[-sentiment_next_not] += 1
				sentiment_next_not = 1
			elif cut[i] in config_not or cut[i] in config_bad:#否定词执行反转
				sentiment_next_not = -sentiment_next_not
	else:#判断前后几个词的否定词计数方式
		sentiment_markers = []
		for i in range(len_cnt):#先将词转化为情感代号
			if cut[i] in config_pos:
				sentiment_markers.append(1)
			elif cut[i] in config_neg:
				sentiment_markers.append(-1)
			elif cut[i] in config_not or cut[i] in config_bad:
				sentiment_markers.append(0)
			else:
				sentiment_markers.append(None)
		if sentiment_config.startswith("+"):#确定右移的上下界
			sentiment_UB = lambda x:min(x + int(sentiment_config[1:]) + 1, len_cnt)#上界记得 +1
			sentiment_LB = lambda x:x
		elif sentiment_config.startswith("-"):#确定左移的上下界
			sentiment_UB = lambda x:x + 1#上界记得 +1
			sentiment_LB = lambda x:max(x - int(sentiment_config[1:]), 0)
		elif sentiment_config.startswith("±"):#确定左移右移的上下界
			sentiment_UB = lambda x:min(x + int(sentiment_config[1:]) + 1, len_cnt)#上界记得 +1
			sentiment_LB = lambda x:max(x - int(sentiment_config[1:]), 0)
		for i in range(len_cut):
			if sentiment_markers[i]:#是情感词
				pos_neg[(-1) ** sentiment_markers[sentiment_LB(i):sentiment_UB(i)].count(0) * sentiment_markers[i]] += 1#取 (-1) ** NOT
	ppp, qqq = pos_neg[1] - pos_neg[-1], pos_neg[1] + pos_neg[-1]#分子和分母
	try:
		rrr = SnowNLP(content).sentiments
	except:
		rrr = nan
	return (pos_neg[1], pos_neg[-1], ppp, qqq, nan if 0 == qqq else ppp / qqq, rrr)

def sentiment_merge(sentiment_any_lists):#合并
	list_T = array(sentiment_any_lists).T.tolist()#转置后求 sum
	a, b, c = sum(list_T[0]), sum(list_T[1]), sum(list_T[2]) / len(list_T[2])
	p, q = a - b, a + b
	return (a, b, p, q, nan if 0 == q else p / q, c)

def sentiment_add_z(tmp_lists):# Z 值标准化
	array_lists = array(tmp_lists).astype(float)
	mean = nanmean(array_lists)#平均值
	std = nanstd(array_lists)#标准差
	if std:
		return ((array_lists - mean) / std).tolist()
	else:
		return [nan for _ in range(array_lists.shape[0])]

def sentiment_is_neighbor(time_1, time_2, sentiment_description):#判断是否为相邻时段
	if "month" == sentiment_description:
		return (										\
			time_2 - time_1 == 1					#同年邻月		\
			or (									\
				time_2 // 100 - time_1 // 100 == 1		#不同年邻年		\
				and								\
				time_1 % 100 - time_2 % 100 == 11		#不同年月份差		\
			)									\
		)
	elif "season" == sentiment_description:
		return (									\
			time_2 - time_1 == 1				#同年邻季度		\
			or (								\
				time_2 // 10 - time_1 // 10 == 1		#不同年邻年		\
				and							\
				time_1 % 10 - time_2 % 10 == 3		#不同年季度差		\
			)								\
		)
	else:
		return time_2 - time_1 == 1

def sentiment_get_last(time_0, sentiment_description):#上一个时间
	if "day" == sentiment_description:
		tmpLast = datetime(time_0 // 10000, time_0 % 10000 // 100, time_0 % 100) - timedelta(1)
		return int(tmpLast.year()) * 10000 + int(tmpLast.month()) * 100 + int(tmpLast.day())
	elif "month" == sentiment_description:
		return time_0 - 89 if time_0 % 100 == 1 else time_0 - 1
	elif "season" == sentiment_description:
		return time_0 - 7 if time_0 % 10 == 1 else time_0 - 1
	else:
		return time_0 - 1

def sentiment_output_bridge(sentiment_ori_tuple, sentiment_any_filepath, sentiment_description):#连接元组和生成文件的大桥
	if "day" == sentiment_description:
		sentiment_any_lists = []
		sentiment_any_dicts = {}
		for ori_tuple in sentiment_ori_tuple:
			try:
				dt = int(ori_tuple[1])#归结到日
			except:
				dt = nan
			sentiment_any_dicts.setdefault(dt, [])
			sentiment_any_dicts[dt].append([ori_tuple[2], ori_tuple[3], ori_tuple[7]])
		for sentiment_key in list(sentiment_any_dicts.keys()):
			sentiment_any_dicts[sentiment_key] = sentiment_merge(sentiment_any_dicts[sentiment_key])
		for sentiment_key in list(sentiment_any_dicts.keys()):
			sentiment_any_lists.append((sentiment_key, ) + sentiment_any_dicts[sentiment_key])
		columns = ["index", "day", "pos_cnt", "neg_cnt", "abs_cnt", "all_cnt", "traditional_sentiment", "nlp_sentiment"]
	elif "week" == sentiment_description:
		sentiment_any_lists = []
		sentiment_any_dicts = {}
		for ori_tuple in sentiment_ori_tuple:
			try:
				y, m, d = int(ori_tuple[1]) // 10000, int(ori_tuple[1]) % 10000 // 100, int(ori_tuple[1]) % 100
				dt = datetime(y, m, d)
				if m in (1, 2):
					m += 12
					y -= 1
				w = (d + (m << 1) + 3 * (m + 1) // 5 + y + (y >> 2) - y // 100 + y // 400) % 7# 0~6 依次为 周一~周日
				dt -= timedelta(w)#归结到每周的第一天
			except:
				dt = nan
			sentiment_any_dicts.setdefault(dt, [])
			sentiment_any_dicts[dt].append([ori_tuple[2], ori_tuple[3], ori_tuple[7]])
		for sentiment_key in list(sentiment_any_dicts.keys()):
			sentiment_any_dicts[sentiment_key] = sentiment_merge(sentiment_any_dicts[sentiment_key])
		for sentiment_key in list(sentiment_any_dicts.keys()):
			sentiment_any_lists.append((sentiment_key, nan if sentiment_key is nan else sentiment_key + timedelta(6)) + sentiment_any_dicts[sentiment_key])
		columns = ["index", "start", "end", "pos_cnt", "neg_cnt", "abs_cnt", "all_cnt", "traditional_sentiment", "nlp_sentiment"]
	elif "month" == sentiment_description:
		sentiment_any_lists = []
		sentiment_any_dicts = {}
		for ori_tuple in sentiment_ori_tuple:
			try:
				dt = int(ori_tuple[1]) // 100#归结到年月
			except:
				dt = nan
			sentiment_any_dicts.setdefault(dt, [])
			sentiment_any_dicts[dt].append([ori_tuple[2], ori_tuple[3], ori_tuple[7]])
		for sentiment_key in list(sentiment_any_dicts.keys()):
			sentiment_any_dicts[sentiment_key] = sentiment_merge(sentiment_any_dicts[sentiment_key])
		for sentiment_key in list(sentiment_any_dicts.keys()):
			sentiment_any_lists.append((sentiment_key, ) + sentiment_any_dicts[sentiment_key])
		columns = ["index", "month", "pos_cnt", "neg_cnt", "abs_cnt", "all_cnt", "traditional_sentiment", "nlp_sentiment"]
	elif "season" == sentiment_description:
		sentiment_any_lists = []
		sentiment_any_dicts = {}
		for ori_tuple in sentiment_ori_tuple:
			try:
				dt = int(ori_tuple[1]) // 10000 * 10 + (int(ori_tuple[1]) % 10000 // 100 - 1) // 3 + 1#归结到季节
			except:
				dt = nan
			sentiment_any_dicts.setdefault(dt, [])
			sentiment_any_dicts[dt].append([ori_tuple[2], ori_tuple[3], ori_tuple[7]])
		for sentiment_key in list(sentiment_any_dicts.keys()):
			sentiment_any_dicts[sentiment_key] = sentiment_merge(sentiment_any_dicts[sentiment_key])
		for sentiment_key in list(sentiment_any_dicts.keys()):
			sentiment_any_lists.append((sentiment_key, ) + sentiment_any_dicts[sentiment_key])
		columns = ["index", "season", "pos_cnt", "neg_cnt", "abs_cnt", "all_cnt", "traditional_sentiment", "nlp_sentiment"]
	elif "year"  == sentiment_description:
		sentiment_any_lists = []
		sentiment_any_dicts = {}
		for ori_tuple in sentiment_ori_tuple:
			try:
				dt = int(ori_tuple[1]) // 10000#归结到年份
			except:
				dt = nan
			sentiment_any_dicts.setdefault(dt, [])
			sentiment_any_dicts[dt].append([ori_tuple[2], ori_tuple[3], ori_tuple[7]])
		for sentiment_key in list(sentiment_any_dicts.keys()):
			sentiment_any_dicts[sentiment_key] = sentiment_merge(sentiment_any_dicts[sentiment_key])
		for sentiment_key in list(sentiment_any_dicts.keys()):
			sentiment_any_lists.append((sentiment_key, ) + sentiment_any_dicts[sentiment_key])
		columns = ["index", "year", "pos_cnt", "neg_cnt", "abs_cnt", "all_cnt", "traditional_sentiment", "nlp_sentiment"]
	elif "decade"  == sentiment_description:
		sentiment_any_lists = []
		sentiment_any_dicts = {}
		for ori_tuple in sentiment_ori_tuple:
			try:
				dt = int(ori_tuple[1]) // 100000#归结到十年
			except:
				dt = nan
			sentiment_any_dicts.setdefault(dt, [])
			sentiment_any_dicts[dt].append([ori_tuple[2], ori_tuple[3], ori_tuple[7]])
		for sentiment_key in list(sentiment_any_dicts.keys()):
			sentiment_any_dicts[sentiment_key] = sentiment_merge(sentiment_any_dicts[sentiment_key])
		for sentiment_key in list(sentiment_any_dicts.keys()):
			sentiment_any_lists.append((nan if sentiment_key is nan else "{0}0s".format(sentiment_key), ) + sentiment_any_dicts[sentiment_key])
		columns = ["index", "decade", "pos_cnt", "neg_cnt", "abs_cnt", "all_cnt", "traditional_sentiment", "nlp_sentiment"]
	elif "century"  == sentiment_description:
		sentiment_any_lists = []
		sentiment_any_dicts = {}
		for ori_tuple in sentiment_ori_tuple:
			try:
				dt = int(ori_tuple[1]) // 1000000#归结到世纪
			except:
				dt = nan
			sentiment_any_dicts.setdefault(dt, [])
			sentiment_any_dicts[dt].append([ori_tuple[2], ori_tuple[3], ori_tuple[7]])
		for sentiment_key in list(sentiment_any_dicts.keys()):
			sentiment_any_dicts[sentiment_key] = sentiment_merge(sentiment_any_dicts[sentiment_key])
		for sentiment_key in list(sentiment_any_dicts.keys()):
			if sentiment_key is nan:
				sentiment_any_lists.append((nan, ) + sentiment_any_dicts[sentiment_key])
			else:
				sentiment_cnt_tmp = (abs(sentiment_key) + 1) * int(sentiment_key / abs(sentiment_key))#计算世纪数
				if abs(sentiment_cnt_tmp) % 10 in (1, 2, 3) and abs(sentiment_cnt_tmp) not in (11, 12, 13):#特殊对待的序数词
					sentiment_cnt_tmp = "{0}{1}".format(sentiment_cnt_tmp, {1:"st", 2:"nd", 3:"rd"}[abs(sentiment_cnt_tmp) % 10])#转为序数词
				else:#可以直接加 th 的序数词
					sentiment_cnt_tmp = "{0}{1}".format(sentiment_cnt_tmp, "th")#转为序数词
				sentiment_any_lists.append(("the {0} century".format(sentiment_cnt_tmp), ) + sentiment_any_dicts[sentiment_key])
		columns = ["index", "century", "pos_cnt", "neg_cnt", "abs_cnt", "all_cnt", "traditional_sentiment", "nlp_sentiment"]
	else:
		sentiment_any_lists = list(sentiment_ori_tuple)
		columns = ["index", "filepath", "date", "pos_cnt", "neg_cnt", "abs_cnt", "all_cnt", "traditional_sentiment", "nlp_sentiment"]
	if sentiment_fill and sentiment_description in ("month", "season"):#如果需要填充不连续的行
		for i in range(len(sentiment_any_lists) - 2, 0, -1):#从后往前遍历
			while not sentiment_is_neighbor(int(sentiment_any_lists[i - 1][0]), int(sentiment_any_lists[i][0]), sentiment_description):#如果不是连续的月则补充
				sentiment_any_lists.insert(i, [sentiment_get_last(int(sentiment_any_lists[i][0]), sentiment_description)] + [0] * 6)
	sentiment_result_length = len(tuple(sentiment_any_lists))
	return result_output_csvexcel(									#输出 csvexcel 数据				\
		sentiment_any_filepath, 								#输出文件路径				\
		DF(										#将二维列表转为 DataFrame 格式		\
			array(									#使用 numpy 的列表执行			\
				[[i for i in range(1, sentiment_result_length + 1)]]				#输出索引				\
				+ array(sentiment_any_lists).T.tolist()										\
				+ [													\
					sentiment_add_z(array(sentiment_any_lists).T.tolist()[-2]), 							\
					sentiment_add_z(array(sentiment_any_lists).T.tolist()[-1])							\
				]													\
			).T.tolist(), 								#转回原二维列表				\
			columns = columns + ["traditional_z", "nlp_z"]					#表头					\
		), 															\
		"Sentiment"														\
	)

def sentiment_walk_folder():#遍历文件并处理
	print_safe("{0} Sentiment: Processing, please wait. ".format(state_symbols[0]))
	sentiment_filepaths = walk_folder()
	if len(sentiment_filepaths) <= 0:
		MessageBox("Sentiment aborted as no input data found. ", -1)
		return False
	sentiment_filepaths = common_sorted(sentiment_filepaths, 3)
	print_safe(sentiment_filepaths)
	print_safe("{0} Sentiment: Successfully gather {1} data. ".format(state_symbols[1], len(sentiment_filepaths)))
	sentiment_progresstext["fg"] = state_fg[0]#进度复原
	sentiment_progressbar["value"] = 0
	sentiment_progressbar["maximum"] = len(sentiment_filepaths)#考虑总样本
	sentiment_progressnum["text"] = "Progress: 0.00%"
	tk.update()
	sentiment_array_tuple = []
	for filepath in sentiment_filepaths:
		print_safe("{0} Sentiment: {1}".format(state_symbols[0], filepath))
		cut = dispose(filepath, sentiment_clears)
		sentiment_tuple = get_sentiments(getContent(filepath), cut)
		sentiment_array_tuple.append((filepath, splitextdate(filepath)[1]) + sentiment_tuple)
		print_safe("{0} Sentiment: {1}".format(state_symbols[1], sentiment_tuple))
		sentiment_progressbar["value"] += 1
		sentiment_progressnum["text"] = "Progress: {0:.2f}%".format(100 * sentiment_progressbar["value"] / sentiment_progressbar["maximum"])
		sentiment_progresstext["text"] = "{0} / {1}".format(sentiment_progressbar["value"], sentiment_progressbar["maximum"])
		tk.update()
	else:#总的
		sentiment_output_flag = True
		sentiment_output_flag = sentiment_output_bridge(sentiment_array_tuple, os.path.join(os.path.join(config_modes["output"], sentiment_paths["folder"]), "file" + os.path.splitext(sentiment_paths["file"])[1]), "file") and sentiment_output_flag
		sentiment_output_flag = sentiment_output_bridge(sentiment_array_tuple, os.path.join(os.path.join(config_modes["output"], sentiment_paths["folder"]), "day" + os.path.splitext(sentiment_paths["file"])[1]), "day") and sentiment_output_flag
		sentiment_output_flag = sentiment_output_bridge(sentiment_array_tuple, os.path.join(os.path.join(config_modes["output"], sentiment_paths["folder"]), "week" + os.path.splitext(sentiment_paths["file"])[1]), "week") and sentiment_output_flag
		sentiment_output_flag = sentiment_output_bridge(sentiment_array_tuple, os.path.join(os.path.join(config_modes["output"], sentiment_paths["folder"]), "month" + os.path.splitext(sentiment_paths["file"])[1]), "month") and sentiment_output_flag
		sentiment_output_flag = sentiment_output_bridge(sentiment_array_tuple, os.path.join(os.path.join(config_modes["output"], sentiment_paths["folder"]), "season" + os.path.splitext(sentiment_paths["file"])[1]), "season") and sentiment_output_flag
		sentiment_output_flag = sentiment_output_bridge(sentiment_array_tuple, os.path.join(os.path.join(config_modes["output"], sentiment_paths["folder"]), "year" + os.path.splitext(sentiment_paths["file"])[1]), "year") and sentiment_output_flag
		sentiment_output_flag = sentiment_output_bridge(sentiment_array_tuple, os.path.join(os.path.join(config_modes["output"], sentiment_paths["folder"]), "decade" + os.path.splitext(sentiment_paths["file"])[1]), "decade") and sentiment_output_flag
		sentiment_output_flag = sentiment_output_bridge(sentiment_array_tuple, os.path.join(os.path.join(config_modes["output"], sentiment_paths["folder"]), "century" + os.path.splitext(sentiment_paths["file"])[1]), "century") and sentiment_output_flag
		if not sentiment_output_flag:
			raise OSError("some files could not be written")
		sentiment_progresstext["fg"] = state_fg[1]#所有操作成功完成
		tk.update()#更新 UI
	return True

def sentiment_main():# Sentiment 主函数
	while True:
		thread_sentiment_lock.acquire()
		if environment_satisfy() is None:#说明需要回收线程了
			break
		sentiment_lockset(DISABLED)
		thread_sentiment_lock.release()#设置为正在运行
		try:
			if sentiment_check_environment() and config_load_userdict("Sentiment") and sentiment_walk_folder():#使用短路逻辑与控制串联流程
				MessageBox("(^_^) Sentiment finished successfully. ", 1)
			else:
				print_safe("{0} Sentiment: Sentiment aborted. ".format(state_symbols[-1]))
		except Exception as sentiment_exception:#进度出错
			if environment_satisfy() is None:#线程被迫中止
				break
			sentiment_progresstext["fg"] = state_fg[-1]#更改主进度颜色
			tk.update()
			MessageBox(")-: Sentiment has some problems and aborted. ", -1)
			print_safe("{0} Sentiment: Sentiment aborted since {1}. ".format(state_symbols[-1], ("\"{0}\"" if str(sentiment_exception)[-1] in (" ", "\t") else "\"{0} \"").format(str(sentiment_exception).replace("\r", "\\r").replace("\n","\\n").replace("\\", "\\\\").replace("\"", "\\\"")) if str(sentiment_exception).replace(" ", "")[-1] in ",;.!" else sentiment_exception))
		thread_sentiment_lock.acquire()#重新上锁
		sentiment_lockset(NORMAL)



# main 函数
def main():
	# System
	print_safe("{0} - Beginning of Process - {1}".format(Global_Title, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
	global tk
	tk = Tk()
	tk.title(Global_Title)
	tk.resizable(0, 0)#阻止调整大小
	tk.geometry()
	tk.protocol("WM_DELETE_WINDOW", lambda:OnCloseMainWindow())
	thread_splitter_lock.acquire()
	thread_similarity_lock.acquire()
	thread_sentiment_lock.acquire()
	thread_splitter = Thread(target = splitter_main, args = ())
	thread_similarity = Thread(target = similarity_main, args = ())
	thread_sentiment = Thread(target = sentiment_main, args = ())
	thread_splitter.daemon = True
	thread_similarity.daemon = True
	thread_sentiment.daemon = True
	thread_splitter.start()
	thread_similarity.start()
	thread_sentiment.start()
	
	# Enviroment
	environment = Frame(tk, relief = RAISED, borderwidth = 2, width = frame_width)
	environment.pack(side = TOP, fill = BOTH, ipadx = frame_pad, ipady = frame_pad, padx = frame_pad, pady = frame_pad)
	environment_label = Label(environment, text = "Environment", font = title_font, fg = title_fg)
	environment_label.pack(side = TOP)
	environment_sub = Frame(environment, relief = FLAT, borderwidth = 2, width = frame_width)
	environment_sub.pack(side = BOTTOM, fill = BOTH, ipady = sub_pad, pady = sub_pad)
	environment_max_length = max([len(items) for items in environment_requirements])
	Label(environment_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 0, column = 0)
	Label(environment_sub, text = "OS: ", font = label_font, fg = state_fg[None]).grid(row = 0, column = 1)
	Label(environment_sub, text = __import__("platform").system(), font = label_font, fg = state_fg[1]).grid(row = 0, column = 2)
	Label(environment_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 0, column = 3)
	if WinOS:#不是 Windows 系统不需要考虑 UAC
		global UAC
		popen_tmp = os.popen("ver")
		UAC = "XP" not in popen_tmp.read().upper()
		popen_tmp.close()
		del popen_tmp
		Label(environment_sub, text = "UAC: ", font = label_font, fg = state_fg[None]).grid(row = 0, column = 4)
		Label(environment_sub, text = "Yes" if UAC else "No", font = label_font, fg = state_fg[1]).grid(row = 0, column = 5)
		Label(environment_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 0, column = 6)
	Label(environment_sub, text = "Environment: ", font = label_font, fg = state_fg[None]).grid(row = 0, column = 7)
	global environment_state_label, environment_btn
	environment_state_label = Label(environment_sub, text = "Not Ready", font = label_font + ("bold", ), fg = state_fg[-1])
	environment_state_label.grid(row = 0, column = 8)
	Label(environment_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 0, column = 9)
	environment_btn = {None:Button(environment_sub, text = "Check All", font = button_font + ("bold", ), fg = state_fg[0], command = lambda:checkall())}
	environment_btn[None].grid(row = 0, column = max(10, environment_max_length + (environment_max_length << 1) - 2), columnspan = 2)
	for i in range(len(environment_requirements)):
		Label(environment_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = i, column = 0)
		for j in range(len(environment_requirements[i])):
			if j == 0 and i == 0:#单独绑定<built-in>（j 放前面运行会更快）
				Label(environment_sub, text = environment_requirements[0][0], font = label_font, fg = state_fg[None], state = DISABLED).grid(row = 1, column = 1)
				exec("environment_btn.setdefault(\"<built-in>\", Button(environment_sub, text = \"checked\", font = button_font, fg = state_fg[1], command = lambda:check(\"<built-in>\")))\nenvironment_btn[\"<built-in>\"].grid(row = 1, column = 2)")
				Label(environment_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 1, column = 3)
			else:
				current_column = j + (j << 1)
				Label(environment_sub, text = environment_requirements[i][j], font = label_font, fg = state_fg[None]).grid(row = i + 1, column = current_column + 1)
				exec("environment_btn.setdefault(\"{0}\", Button(environment_sub, text = \"check\", font = button_font, fg = state_fg[0], command = lambda:check(\"{0}\")))\nenvironment_btn[\"{0}\"].grid(row = i + 1, column = current_column + 2)".format(environment_requirements[i][j]))
				Label(environment_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = i + 1, column = current_column + 3)
	
	# Config
	config = Frame(tk, relief = RAISED, borderwidth = 2, width = frame_width)
	config.pack(side = TOP, fill = BOTH, ipadx = frame_pad, ipady = frame_pad, padx = frame_pad, pady = frame_pad)
	config_label = Label(config, text = "Config", font = title_font, fg = title_fg)
	config_label.pack(side = TOP)
	config_sub = Frame(config, relief = FLAT, borderwidth = 2, width = frame_width)
	config_sub.pack(side = BOTTOM, fill = BOTH, ipady = sub_pad, pady = sub_pad)
	config_tmp_counter = 0
	for config_key in list(config_paths.keys()):
		Label(config_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = config_tmp_counter % 3, column = config_tmp_counter // 3 * 5)
		Label(config_sub, text = config_key + ": ", font = label_font, fg = state_fg[None]).grid(row = config_tmp_counter % 3, column = config_tmp_counter // 3 * 5 + 1)
		config_displayers[config_key] = StringVar()
		config_displayers[config_key].set(str(config_paths[config_key]))
		Entry(config_sub, textvariable = config_displayers[config_key], font = label_font, fg = state_fg[None], state = "readonly", width = entry_width).grid(row = config_tmp_counter % 3, column = config_tmp_counter // 3 * 5 + 2)
		Label(config_sub, text = "  ", font = label_font, fg = state_fg[None]).grid(row = config_tmp_counter % 3, column = config_tmp_counter // 3 * 5 + 3)
		exec("{0} = Button(config_sub, text = \" .. \", font = button_font, fg = state_fg[0], command = lambda:getpath(\"{1}\"))\n{0}.grid(row = config_tmp_counter % 3, column = config_tmp_counter // 3 * 5 + 4)\nconfig_controllers.add({0})".format("config_btn_{0}".format(config_tmp_counter), config_key))
		config_tmp_counter += 1
	global config_split_sv, config_combobox, config_ety_sv_log, config_ety_sv_output
	config_last_column = config_tmp_counter // 3 * 5 + 1#定位到最后一列
	for i in range(3):
		for j in (0, 3):#注意没有 range
			Label(config_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = i, column = config_last_column + j)# delims
	Label(config_sub, text = "mode: ", font = label_font, fg = state_fg[None]).grid(row = 0, column = config_last_column + 1)# begin of split_mode
	config_split_sv, config_ety_sv_log, config_ety_sv_output = StringVar(), StringVar(), StringVar()# Initial three string vars
	config_split_sv.set(config_values[config_modes["mode"]])
	config_ety_sv_log.set(config_modes["log"])
	config_ety_sv_output.set(config_modes["output"])
	config_combobox = Combobox(config_sub, textvariable = config_split_sv, value = config_values, state = "readonly", width = entry_width)
	config_combobox.current(0)
	config_combobox.grid(row = 0, column = config_last_column + 2)
	config_combobox.bind("<<ComboboxSelected>>", set_split_method)# end of split_mode
	Label(config_sub, text = "log: ", font = label_font, fg = state_fg[None]).grid(row = 1, column = config_last_column + 1)# begin of log
	config_ety_controller_log = Entry(config_sub, textvariable = config_ety_sv_log, font = label_font, fg = state_fg[None], state = NORMAL, width = entry_width)
	config_ety_controller_log.bind("<FocusOut>", config_ety_change_log)
	config_ety_controller_log.grid(row = 1, column = config_last_column + 2)
	config_controllers.add(config_ety_controller_log)# end of log
	Label(config_sub, text = "output: ", font = label_font, fg = state_fg[None]).grid(row = 2, column = config_last_column + 1)# begin of output
	config_ety_controller_output = Entry(config_sub, textvariable = config_ety_sv_output, font = label_font, fg = state_fg[None], state = NORMAL, width = entry_width)
	config_ety_controller_output.bind("<FocusOut>", config_ety_change_output)
	config_ety_controller_output.grid(row = 2, column = config_last_column + 2)
	config_controllers.add(config_ety_controller_output)# end of output
	
	# Splitter
	splitter = Frame(tk, relief = RAISED, borderwidth = 2, width = frame_width)
	splitter.pack(side = TOP, fill = BOTH, ipadx = frame_pad, ipady = frame_pad, padx = frame_pad, pady = frame_pad)
	splitter_label = Label(splitter, text = "Splitter", font = title_font, fg = title_fg)
	splitter_label.pack(side = TOP)
	splitter_sub = Frame(splitter, relief = FLAT, borderwidth = 2, width = frame_width)
	splitter_sub.pack(side = BOTTOM, fill = BOTH, ipady = sub_pad, pady = sub_pad)
	for i in range(len(splitter_paths) + 3):#先巧妙地生成第一第二行的列间隔
		Label(splitter_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 0, column = i << 1)
		Label(splitter_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 1, column = i << 1)
	Label(splitter_sub, text = "File", font = label_font, fg = state_fg[None]).grid(row = 0, column = 1)
	Label(splitter_sub, text = "Folder", font = label_font, fg = state_fg[None]).grid(row = 0, column = 3)
	Label(splitter_sub, text = "Wordcloud", font = label_font, fg = state_fg[None]).grid(row = 0, column = 5)
	global splitter_btn_lock, splitter_btn_clear, splitter_btn_run, splitter_sv_file, splitter_sv_folder, splitter_sv_wordcloud, splitter_progressnum, splitter_progressbar, splitter_progresstext
	splitter_clears["space"], splitter_clears["digits"], splitter_clears["stopwords"] = BooleanVar(), BooleanVar(), BooleanVar()
	splitter_clears["space"].set(True)
	splitter_clears["digits"].set(True)
	splitter_clears["stopwords"].set(True)
	splitter_sv_file, splitter_sv_folder, splitter_sv_wordcloud = StringVar(), StringVar(), StringVar()
	splitter_sv_file.set(splitter_paths["file"])
	splitter_sv_folder.set(splitter_paths["folder"])
	splitter_sv_wordcloud.set(splitter_paths["wordcloud"])
	Label(splitter_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 1, column = 0)
	splitter_chk_space = Checkbutton(splitter_sub, text = "Clear Space", variable = splitter_clears["space"], onvalue = True, offvalue = False, font = label_font, fg = state_fg[None])
	splitter_chk_space.grid(row = 0, column = 7)
	splitter_chk_return = Checkbutton(splitter_sub, text = "Clear Digits", variable = splitter_clears["digits"], onvalue = True, offvalue = False, font = label_font, fg = state_fg[None])
	splitter_chk_return.grid(row = 0, column = 9)
	splitter_chk_digits = Checkbutton(splitter_sub, text = "Clear Stopwords", variable = splitter_clears["stopwords"], onvalue = True, offvalue = False, font = label_font, fg = state_fg[None])
	splitter_chk_digits.grid(row = 0, column = 11)
	splitter_ety_file = Entry(splitter_sub, text = splitter_sv_file, font = label_font, fg = state_fg[None], state = NORMAL, width = entry_width)
	splitter_ety_file.grid(row = 1, column = 1)
	splitter_ety_file.bind("<FocusOut>", splitter_ety_change_file)
	splitter_ety_folder = Entry(splitter_sub, text = splitter_sv_folder, font = label_font, fg = state_fg[None], state = NORMAL, width = entry_width)
	splitter_ety_folder.grid(row = 1, column = 3)
	splitter_ety_folder.bind("<FocusOut>", splitter_ety_change_folder)
	splitter_ety_wordcloud = Entry(splitter_sub, text = splitter_sv_wordcloud, font = label_font, fg = state_fg[None], state = NORMAL, width = entry_width)
	splitter_ety_wordcloud.grid(row = 1, column = 5)
	splitter_ety_wordcloud.bind("<FocusOut>", splitter_ety_change_wordcloud)
	splitter_controllers.update({splitter_chk_space, splitter_chk_return, splitter_chk_digits, splitter_ety_file, splitter_ety_folder, splitter_ety_wordcloud})#添加所有需要群控的控件标签
	splitter_btn_lock = Button(splitter_sub, text = "Lock: Off", font = button_font, fg = state_fg[0], command = lambda:splitter_lock())
	splitter_btn_lock.grid(row = 1, column = 7)
	splitter_btn_clear = Button(splitter_sub, text = "Clear Results", font = button_font, fg = state_fg[-1], command = lambda:clear("Splitter"), state = DISABLED)
	splitter_btn_clear.grid(row = 1, column = 9)
	splitter_btn_run = Button(splitter_sub, text = "Run Splitter", font = button_font + ("bold", ), fg = state_fg[-1], command = lambda:thread_splitter_lock.release(), state = DISABLED)
	splitter_btn_run.grid(row = 1, column = 11)
	Label(splitter_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 2, column = 0)
	splitter_progressnum = Label(splitter_sub, text = "Progress: 100.00%", font = label_font, fg = state_fg[None])
	splitter_progressnum.grid(row = 2, column = 1, columnspan = 2)
	splitter_progressbar = Progressbar(splitter_sub, length = progressbar_width, orient = HORIZONTAL, mode = "determinate", takefocus = False)
	splitter_progressbar.grid(row = 2, column = 3, columnspan = 8)
	splitter_progressbar["maximum"] = progressbar_width
	splitter_progressbar["value"] = progressbar_width
	splitter_progresstext = Label(splitter_sub, text = " " * grid_pad, font = label_font, fg = state_fg[0])
	splitter_progresstext.grid(row = 2, column = 11)
	Label(splitter_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 2, column = 12)
	
	# Similarity
	similarity = Frame(tk, relief = RAISED, borderwidth = 2, width = frame_width)
	similarity.pack(side = TOP, fill = BOTH, ipadx = frame_pad, ipady = frame_pad, padx = frame_pad, pady = frame_pad)
	similarity_label = Label(similarity, text = "Similarity", font = title_font, fg = title_fg)
	similarity_label.pack(side = TOP)
	similarity_sub = Frame(similarity, relief = FLAT, borderwidth = 2, width = frame_width)
	similarity_sub.pack(side = BOTTOM, fill = BOTH, ipady = sub_pad, pady = sub_pad)
	for i in range(len(similarity_paths) + 3):#先巧妙地生成第一第二行的列间隔
		Label(similarity_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 0, column = i << 1)
		Label(similarity_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 1, column = i << 1)
	Label(similarity_sub, text = "File", font = label_font, fg = state_fg[None]).grid(row = 0, column = 1)
	Label(similarity_sub, text = "Folder", font = label_font, fg = state_fg[None]).grid(row = 0, column = 3)
	Label(similarity_sub, text = "Order", font = label_font, fg = state_fg[None]).grid(row = 0, column = 5)
	global similarity_btn_lock, similarity_btn_clear, similarity_btn_run, similarity_sv_file, similarity_sv_folder, similarity_order_sv, similarity_combobox
	global similarity_progressnum_main, similarity_progressbar_main, similarity_progresstext_main#主进度条
	global similarity_progressnum_sub, similarity_progressbar_sub, similarity_progresstext_sub#子进度条
	similarity_clears["space"], similarity_clears["digits"], similarity_clears["stopwords"] = BooleanVar(), BooleanVar(), BooleanVar()
	similarity_clears["space"].set(True)
	similarity_clears["digits"].set(True)
	similarity_clears["stopwords"].set(True)
	similarity_sv_file, similarity_sv_folder, similarity_order_sv = StringVar(), StringVar(), StringVar()
	similarity_sv_file.set(similarity_paths["file"])
	similarity_sv_folder.set(similarity_paths["folder"])
	Label(similarity_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 1, column = 0)
	similarity_chk_space = Checkbutton(similarity_sub, text = "Clear Space", variable = similarity_clears["space"], onvalue = True, offvalue = False, font = label_font, fg = state_fg[None])
	similarity_chk_space.grid(row = 0, column = 7)
	similarity_chk_return = Checkbutton(similarity_sub, text = "Clear Digits", variable = similarity_clears["digits"], onvalue = True, offvalue = False, font = label_font, fg = state_fg[None])
	similarity_chk_return.grid(row = 0, column = 9)
	similarity_chk_digits = Checkbutton(similarity_sub, text = "Clear Stopwords", variable = similarity_clears["stopwords"], onvalue = True, offvalue = False, font = label_font, fg = state_fg[None])
	similarity_chk_digits.grid(row = 0, column = 11)
	similarity_ety_file = Entry(similarity_sub, text = similarity_sv_file, font = label_font, fg = state_fg[None], state = NORMAL, width = entry_width)
	similarity_ety_file.grid(row = 1, column = 1)
	similarity_ety_file.bind("<FocusOut>", similarity_ety_change_file)
	similarity_ety_folder = Entry(similarity_sub, text = similarity_sv_folder, font = label_font, fg = state_fg[None], state = NORMAL, width = entry_width)
	similarity_ety_folder.grid(row = 1, column = 3)
	similarity_ety_folder.bind("<FocusOut>", similarity_ety_change_folder)
	similarity_combobox = Combobox(similarity_sub, textvariable = similarity_order_sv, value = similarity_values, width = entry_width, state = "readonly")
	similarity_combobox.current(3)#建议用时间排序
	similarity_combobox.grid(row = 1, column = 5)
	similarity_combobox.bind("<<ComboboxSelected>>", set_similarity_order)
	similarity_controllers.update({similarity_chk_space, similarity_chk_return, similarity_chk_digits, similarity_ety_file, similarity_ety_folder})#添加所有需要群控的控件标签
	similarity_btn_lock = Button(similarity_sub, text = "Lock: Off", font = button_font, fg = state_fg[0], command = lambda:similarity_lock())
	similarity_btn_lock.grid(row = 1, column = 7)
	similarity_btn_clear = Button(similarity_sub, text = "Clear Results", font = button_font, fg = state_fg[-1], command = lambda:clear("Similarity"), state = DISABLED)
	similarity_btn_clear.grid(row = 1, column = 9)
	similarity_btn_run = Button(similarity_sub, text = "Run Similarity", font = button_font + ("bold", ), fg = state_fg[-1], command = lambda:thread_similarity_lock.release(), state = DISABLED)
	similarity_btn_run.grid(row = 1, column = 11)
	Label(similarity_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 2, column = 0)# begin of main progressbar
	similarity_progressnum_main = Label(similarity_sub, text = "Main: 100.00%", font = label_font, fg = state_fg[None])
	similarity_progressnum_main.grid(row = 2, column = 1, columnspan = 2)
	similarity_progressbar_main = Progressbar(similarity_sub, length = progressbar_width, orient = HORIZONTAL, mode = "determinate", takefocus = False)
	similarity_progressbar_main.grid(row = 2, column = 3, columnspan = 8)
	similarity_progressbar_main["maximum"] = progressbar_width
	similarity_progressbar_main["value"] = progressbar_width
	similarity_progresstext_main = Label(similarity_sub, text = " " * grid_pad, font = label_font, fg = state_fg[0])
	similarity_progresstext_main.grid(row = 2, column = 11)
	Label(similarity_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 2, column = 12)# end of main progressbar
	Label(similarity_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 3, column = 0)# begin of sub progressbar
	similarity_progressnum_sub = Label(similarity_sub, text = "Sub: 100.00%", font = label_font, fg = state_fg[None])
	similarity_progressnum_sub.grid(row = 3, column = 1, columnspan = 2)
	similarity_progressbar_sub = Progressbar(similarity_sub, length = progressbar_width, orient = HORIZONTAL, mode = "determinate", takefocus = False)
	similarity_progressbar_sub.grid(row = 3, column = 3, columnspan = 8)
	similarity_progressbar_sub["maximum"] = progressbar_width
	similarity_progressbar_sub["value"] = progressbar_width
	similarity_progresstext_sub = Label(similarity_sub, text = " " * grid_pad, font = label_font, fg = state_fg[0])
	similarity_progresstext_sub.grid(row = 3, column = 11)
	Label(similarity_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 3, column = 12)# end of sub progressbar
	
	# Sentiment
	sentiment = Frame(tk, relief = RAISED, borderwidth = 2, width = frame_width)
	sentiment.pack(side = TOP, fill = BOTH, ipadx = frame_pad, ipady = frame_pad, padx = frame_pad, pady = frame_pad)
	sentiment_label = Label(sentiment, text = "Sentiment", font = title_font, fg = title_fg)
	sentiment_label.pack(side = TOP)
	sentiment_sub = Frame(sentiment, relief = FLAT, borderwidth = 2, width = frame_width)
	sentiment_sub.pack(side = BOTTOM, fill = BOTH, ipady = sub_pad, pady = sub_pad)
	for i in range(len(sentiment_paths) + 3):#先巧妙地生成第一第二行的列间隔
		Label(sentiment_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 0, column = i << 1)
		Label(sentiment_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 1, column = i << 1)
	Label(sentiment_sub, text = "File", font = label_font, fg = state_fg[None]).grid(row = 0, column = 1)
	Label(sentiment_sub, text = "Folder", font = label_font, fg = state_fg[None]).grid(row = 0, column = 3)
	Label(sentiment_sub, text = "NOT", font = label_font, fg = state_fg[None]).grid(row = 0, column = 5)
	global sentiment_btn_lock, sentiment_btn_clear, sentiment_btn_run, sentiment_sv_file, sentiment_sv_folder, sentiment_order_sv, sentiment_combobox
	global sentiment_progressnum, sentiment_progressbar, sentiment_progresstext#主进度条
	sentiment_clears["space"], sentiment_clears["digits"], sentiment_clears["stopwords"] = BooleanVar(), BooleanVar(), BooleanVar()
	sentiment_clears["space"].set(True)
	sentiment_clears["digits"].set(True)
	sentiment_clears["stopwords"].set(True)
	sentiment_sv_file, sentiment_sv_folder, sentiment_order_sv = StringVar(), StringVar(), StringVar()
	sentiment_sv_file.set(sentiment_paths["file"])
	sentiment_sv_folder.set(sentiment_paths["folder"])
	Label(sentiment_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 1, column = 0)
	sentiment_chk_space = Checkbutton(sentiment_sub, text = "Clear Space", variable = sentiment_clears["space"], onvalue = True, offvalue = False, font = label_font, fg = state_fg[None])
	sentiment_chk_space.grid(row = 0, column = 7)
	sentiment_chk_return = Checkbutton(sentiment_sub, text = "Clear Digits", variable = sentiment_clears["digits"], onvalue = True, offvalue = False, font = label_font, fg = state_fg[None])
	sentiment_chk_return.grid(row = 0, column = 9)
	sentiment_chk_digits = Checkbutton(sentiment_sub, text = "Clear Stopwords", variable = sentiment_clears["stopwords"], onvalue = True, offvalue = False, font = label_font, fg = state_fg[None])
	sentiment_chk_digits.grid(row = 0, column = 11)
	sentiment_ety_file = Entry(sentiment_sub, text = sentiment_sv_file, font = label_font, fg = state_fg[None], state = NORMAL, width = entry_width)
	sentiment_ety_file.grid(row = 1, column = 1)
	sentiment_ety_file.bind("<FocusOut>", sentiment_ety_change_file)
	sentiment_ety_folder = Entry(sentiment_sub, text = sentiment_sv_folder, font = label_font, fg = state_fg[None], state = NORMAL, width = entry_width)
	sentiment_ety_folder.grid(row = 1, column = 3)
	sentiment_ety_folder.bind("<FocusOut>", sentiment_ety_change_folder)
	sentiment_combobox = Combobox(sentiment_sub, textvariable = sentiment_order_sv, value = sentiment_values, width = entry_width, state = "readonly")
	sentiment_combobox.current(9)#建议用 -4
	sentiment_combobox.grid(row = 1, column = 5)
	sentiment_combobox.bind("<<ComboboxSelected>>", set_sentiment_order)
	sentiment_controllers.update({sentiment_chk_space, sentiment_chk_return, sentiment_chk_digits, sentiment_ety_file, sentiment_ety_folder})#添加所有需要群控的控件标签
	sentiment_btn_lock = Button(sentiment_sub, text = "Lock: Off", font = button_font, fg = state_fg[0], command = lambda:sentiment_lock())
	sentiment_btn_lock.grid(row = 1, column = 7)
	sentiment_btn_clear = Button(sentiment_sub, text = "Clear Results", font = button_font, fg = state_fg[-1], command = lambda:clear("Sentiment"), state = DISABLED)
	sentiment_btn_clear.grid(row = 1, column = 9)
	sentiment_btn_run = Button(sentiment_sub, text = "Run Sentiment", font = button_font + ("bold", ), fg = state_fg[-1], command = lambda:thread_sentiment_lock.release(), state = DISABLED)
	sentiment_btn_run.grid(row = 1, column = 11)
	Label(sentiment_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 2, column = 0)# begin of main progressbar
	sentiment_progressnum = Label(sentiment_sub, text = "Main: 100.00%", font = label_font, fg = state_fg[None])
	sentiment_progressnum.grid(row = 2, column = 1, columnspan = 2)
	sentiment_progressbar = Progressbar(sentiment_sub, length = progressbar_width, orient = HORIZONTAL, mode = "determinate", takefocus = False)
	sentiment_progressbar.grid(row = 2, column = 3, columnspan = 8)
	sentiment_progressbar["maximum"] = progressbar_width
	sentiment_progressbar["value"] = progressbar_width
	sentiment_progresstext = Label(sentiment_sub, text = " " * grid_pad, font = label_font, fg = state_fg[0])
	sentiment_progresstext.grid(row = 2, column = 11)
	Label(sentiment_sub, text = " " * grid_pad, font = label_font, fg = state_fg[None]).grid(row = 2, column = 12)# end of main progressbar
	
	# Mainloop
	try:
		tk.mainloop()
	except:
		pass
	global config_stdout
	if environment_satisfy() is None:
		return EXIT_FAILURE
	Environment_State.set(None)#停止线程
	thread_splitter_lock.release()
	thread_similarity_lock.release()
	thread_sentiment_lock.release()
	thread_splitter.join()
	thread_similarity.join()
	thread_sentiment.join()
	thread_splitter_lock.release()#重置锁
	thread_similarity_lock.release()
	thread_sentiment_lock.release()
	if config_stdout != config_ori_std:
		print_safe("{0} Mainloop: The main window has been closed. \n{1} Thank you for using. ".format(state_symbols[None], state_symbols[None]))
		print_safe("{0} - End of Log - {1}".format(Global_Title, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
		config_stdout.close()#关闭文件防止漏洞
	config_stdout = config_ori_std#切换回控制台
	print_safe("{0} Mainloop: The main window has been closed. \n{1} Thank you for using. ".format(state_symbols[None], state_symbols[None]))
	print_safe("{0} - End of Process - {1}".format(Global_Title, datetime.now().strftime("%Y-%m-%d %H:%M:%S")))
	return EXIT_SUCCESS





# Python 编程规范
if __name__  ==  "__main__":
	sys.exit(main())