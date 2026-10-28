#!/usr/bin/env python3
# -*- coding: utf-8 -*-
import os
import sys
import json
from datetime import datetime

os.environ["TK_SILENCE_DEPRECATION"] = "1"

import re
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import tkinter.font as tkfont

ARCHIVO_PERSISTENCIA = os.path.join(os.path.dirname(os.path.abspath(__file__)), "reglas_guardadas.json")



class MotorInferenciaTableau:
    def __init__(self):
        self.tabla_atomos = {}  
        self.inverso_atomos = {} 
        self.contador_atomos = ord('p')

    def obtener_o_crear_atomo(self, texto_atomo):
        texto_atomo = texto_atomo.strip().lower().replace("«", "").replace("»", "").replace(",", "").replace(".", "").strip()
        if texto_atomo in self.tabla_atomos:
            return self.tabla_atomos[texto_atomo]
        if self.contador_atomos > ord('z'):
            raise Exception("Se han agotado las letras disponibles para átomos.")
        letra = chr(self.contador_atomos)
        self.contador_atomos += 1
        self.tabla_atomos[texto_atomo] = letra
        self.inverso_atomos[letra] = texto_atomo
        return letra

    def parsear_proposicion(self, texto):
        texto = texto.strip().lower().replace("«", "").replace("»", "").strip()
        if " si y solo si " in texto:
            partes = texto.split(" si y solo si ")
            return ('iff', self.parsear_proposicion(partes[0]), self.parsear_proposicion(partes[1]))
        if texto.startswith("si "):
            if " entonces " not in texto:
                raise ValueError(f"Sintaxis incorrecta en regla: '{texto}'. Falta 'entonces'.")
            partes = texto[3:].split(" entonces ")
            return ('implies', self.parsear_proposicion(partes[0]), self.parsear_proposicion(partes[1]))
        if " o " in texto:
            partes = texto.split(" o ")
            return ('or', self.parsear_proposicion(partes[0]), self.parsear_proposicion(partes[1]))
        if " y " in texto:
            partes = texto.split(" y ")
            return ('and', self.parsear_proposicion(partes[0]), self.parsear_proposicion(partes[1]))
        if texto.startswith("no "):
            sub_formula = self.parsear_proposicion(texto[3:])
            return ('not', sub_formula)
        letra = self.obtener_o_crear_atomo(texto)
        return ('atom', letra)

    def formula_a_string(self, f):
        if f[0] == 'atom':
            return f[1]
        elif f[0] == 'not':
            sub = self.formula_a_string(f[1])
            return f"¬{sub}" if f[1][0] == 'atom' else f"¬({sub})"
        elif f[0] == 'and':
            return f"({self.formula_a_string(f[1])} ∧ {self.formula_a_string(f[2])})"
        elif f[0] == 'or':
            return f"({self.formula_a_string(f[1])} ∨ {self.formula_a_string(f[2])})"
        elif f[0] == 'implies':
            return f"({self.formula_a_string(f[1])} → {self.formula_a_string(f[2])})"
        elif f[0] == 'iff':
            return f"({self.formula_a_string(f[1])} ↔ {self.formula_a_string(f[2])})"
        return ""

def es_literal(f):
    if f[0] == 'atom':
        return True
    if f[0] == 'not' and f[1][0] == 'atom':
        return True
    return False

def branch_es_contradictoria(formulas):
    pos = set()
    neg = set()
    for f in formulas:
        if f[0] == 'atom':
            pos.add(f[1])
        elif f[0] == 'not' and f[1][0] == 'atom':
            neg.add(f[1][1])
    return not pos.isdisjoint(neg)

def copy_branch(b):
    return {
        'id': b['id'],
        'formulas': list(b['formulas']),
        'unprocessed': list(b['unprocessed'])
    }

def resolver_tableau(formulas_iniciales):
    initial_branch = {
        'id': '1',
        'formulas': list(formulas_iniciales),
        'unprocessed': list(formulas_iniciales)
    }
    
    branches = [initial_branch]
    finished_branches = []
    
    while branches:
        current = branches.pop(0)
        
        if branch_es_contradictoria(current['formulas']):
            current['closed'] = True
            finished_branches.append(current)
            continue
            
        next_f = None
        found_idx = -1
        for i, f in enumerate(current['unprocessed']):
            if not es_literal(f):
                next_f = f
                found_idx = i
                break
        
        if next_f is None:
            current['closed'] = False
            finished_branches.append(current)
            continue
            
        current['unprocessed'].pop(found_idx)
        tipo = next_f[0]
        
        if tipo == 'not':
            sub = next_f[1]
            sub_tipo = sub[0]
            if sub_tipo == 'atom':
                branches.insert(0, current)
            elif sub_tipo == 'not':
                f_new = sub[1]
                if f_new not in current['formulas']:
                    current['formulas'].append(f_new)
                    current['unprocessed'].append(f_new)
                branches.insert(0, current)
            elif sub_tipo == 'and':
                f1, f2 = sub[1], sub[2]
                not_f1 = ('not', f1)
                not_f2 = ('not', f2)
                
                b1 = copy_branch(current)
                b1['id'] += '.1'
                if not_f1 not in b1['formulas']:
                    b1['formulas'].append(not_f1)
                    b1['unprocessed'].append(not_f1)
                
                b2 = copy_branch(current)
                b2['id'] += '.2'
                if not_f2 not in b2['formulas']:
                    b2['formulas'].append(not_f2)
                    b2['unprocessed'].append(not_f2)
                    
                branches.insert(0, b1)
                branches.insert(0, b2)
            elif sub_tipo == 'or':
                not_sub1 = ('not', sub[1])
                not_sub2 = ('not', sub[2])
                if not_sub1 not in current['formulas']:
                    current['formulas'].append(not_sub1)
                    current['unprocessed'].append(not_sub1)
                if not_sub2 not in current['formulas']:
                    current['formulas'].append(not_sub2)
                    current['unprocessed'].append(not_sub2)
                branches.insert(0, current)
            elif sub_tipo == 'implies':
                f1, f2 = sub[1], sub[2]
                not_f2 = ('not', f2)
                if f1 not in current['formulas']:
                    current['formulas'].append(f1)
                    current['unprocessed'].append(f1)
                if not_f2 not in current['formulas']:
                    current['formulas'].append(not_f2)
                    current['unprocessed'].append(not_f2)
                branches.insert(0, current)
            elif sub_tipo == 'iff':
                f1, f2 = sub[1], sub[2]
                not_f1 = ('not', f1)
                not_f2 = ('not', f2)
                
                b1 = copy_branch(current)
                b1['id'] += '.a'
                for fx in [f1, not_f2]:
                    if fx not in b1['formulas']:
                        b1['formulas'].append(fx)
                        b1['unprocessed'].append(fx)
                        
                b2 = copy_branch(current)
                b2['id'] += '.b'
                for fx in [not_f1, f2]:
                    if fx not in b2['formulas']:
                        b2['formulas'].append(fx)
                        b2['unprocessed'].append(fx)
                        
                branches.insert(0, b1)
                branches.insert(0, b2)
        elif tipo == 'and':
            f1, f2 = next_f[1], next_f[2]
            if f1 not in current['formulas']:
                current['formulas'].append(f1)
                current['unprocessed'].append(f1)
            if f2 not in current['formulas']:
                current['formulas'].append(f2)
                current['unprocessed'].append(f2)
            branches.insert(0, current)
        elif tipo == 'or':
            f1, f2 = next_f[1], next_f[2]
            b1 = copy_branch(current)
            b1['id'] += '.a'
            if f1 not in b1['formulas']:
                b1['formulas'].append(f1)
                b1['unprocessed'].append(f1)
            b2 = copy_branch(current)
            b2['id'] += '.b'
            if f2 not in b2['formulas']:
                b2['formulas'].append(f2)
                b2['unprocessed'].append(f2)
            branches.insert(0, b1)
            branches.insert(0, b2)
        elif tipo == 'implies':
            f1, f2 = next_f[1], next_f[2]
            not_f1 = ('not', f1)
            
            b1 = copy_branch(current)
            b1['id'] += '.a'
            if not_f1 not in b1['formulas']:
                b1['formulas'].append(not_f1)
                b1['unprocessed'].append(not_f1)
            b2 = copy_branch(current)
            b2['id'] += '.b'
            if f2 not in b2['formulas']:
                b2['formulas'].append(f2)
                b2['unprocessed'].append(f2)
            branches.insert(0, b1)
            branches.insert(0, b2)
        elif tipo == 'iff':
            f1, f2 = next_f[1], next_f[2]
            not_f1 = ('not', f1)
            not_f2 = ('not', f2)
            
            b1 = copy_branch(current)
            b1['id'] += '.1'
            for fx in [f1, f2]:
                if fx not in b1['formulas']:
                    b1['formulas'].append(fx)
                    b1['unprocessed'].append(fx)
                    
            b2 = copy_branch(current)
            b2['id'] += '.2'
            for fx in [not_f1, not_f2]:
                if fx not in b2['formulas']:
                    b2['formulas'].append(fx)
                    b2['unprocessed'].append(fx)
                    
            branches.insert(0, b1)
            branches.insert(0, b2)
            
    return finished_branches


# ======================================================================
#  ÁRBOL: se reconstruye a partir de los ids de las ramas finales
#  ('1', '1.a', '1.a.2', ...). El padre de un id es el id sin su último tramo.
# ======================================================================

def atomos_contradictorios(formulas):
    pos, neg = set(), set()
    for f in formulas:
        if f[0] == 'atom':
            pos.add(f[1])
        elif f[0] == 'not' and f[1][0] == 'atom':
            neg.add(f[1][1])
    return sorted(pos & neg)


def acumular(nodo):
    """Fórmulas que ya existían en el nodo al momento de ramificar."""
    if not nodo['hijos']:
        nodo['acum'] = nodo['rama']['formulas']
        return nodo['acum']
    listas = [acumular(h) for h in nodo['hijos']]
    comunes = []
    for items in zip(*listas):
        if all(x == items[0] for x in items):
            comunes.append(items[0])
        else:
            break
    nodo['acum'] = comunes
    return comunes


def construir_arbol(ramas):
    nodos = {}
    for r in ramas:
        partes = r['id'].split('.')
        for k in range(1, len(partes) + 1):
            id_ = '.'.join(partes[:k])
            nodo = nodos.setdefault(id_, {'id': id_, 'hijos': [], 'rama': None})
            if k > 1:
                padre = nodos['.'.join(partes[:k - 1])]
                if id_ not in [h['id'] for h in padre['hijos']]:
                    padre['hijos'].append(nodo)
        nodos[r['id']]['rama'] = r
    for nodo in nodos.values():
        nodo['hijos'].sort(key=lambda h: h['id'].rsplit('.', 1)[1])
    raiz = nodos['1']
    acumular(raiz)
    return raiz


def recorrer(nodo, previo=0):
    nodo['previo'] = previo
    lista = [nodo]
    for h in nodo['hijos']:
        lista += recorrer(h, len(nodo['acum']))
    return lista


def disponer(raiz, sep_x, sep_y, x0=0):
    """Asigna cx (centro) e y (borde superior) a cada nodo. Requiere n['w'] y n['h']."""
    def ancho(n):
        hijos = n['hijos']
        total = sum(ancho(h) for h in hijos) + sep_x * max(len(hijos) - 1, 0)
        n['sw'] = max(n['w'], total)
        return n['sw']

    alturas = {}
    def niveles(n, d):
        n['nivel'] = d
        alturas[d] = max(alturas.get(d, 0), n['h'])
        for h in n['hijos']:
            niveles(h, d + 1)

    def colocar(n, izq):
        n['cx'] = izq + n['sw'] / 2
        n['y'] = tops[n['nivel']]
        hijos = n['hijos']
        total = sum(h['sw'] for h in hijos) + sep_x * max(len(hijos) - 1, 0)
        x = izq + (n['sw'] - total) / 2
        for h in hijos:
            colocar(h, x)
            x += h['sw'] + sep_x

    ancho(raiz)
    niveles(raiz, 0)
    tops, y = {}, 0
    for d in sorted(alturas):
        tops[d] = y
        y += alturas[d] + sep_y
    colocar(raiz, x0)


# ======================================================================
#  INTERFAZ
# ======================================================================

BG = "#f3f4f6"
PANEL = "#ffffff"
BORDE = "#cfd5dc"
TEXTO = "#1f2933"
SUAVE = "#6b7785"
ACENTO = "#2f5d8a"
ACENTO_SUAVE = "#dbe7f3"
OK, OK_FONDO = "#1e8449", "#e6f4ea"
MAL, MAL_FONDO = "#b03a2e", "#fbeae8"
MEDIO, MEDIO_FONDO = "#5d6d7e", "#eef1f5"
LINEA = "#9aa5b1"

PAD_X, PAD_Y, PAD_CAB = 12, 8, 5
SEP_X, SEP_Y = 28, 46

EJEMPLO = [
    "estudio si y solo si tengo el libro",
    "si tengo el libro y leo, entonces apruebo",
    "estudio o leo",
    "no apruebo",
    "no tengo el libro",
]


class App:
    def __init__(self, raiz):
        self.raiz = raiz
        self.reglas = []
        self.motor = MotorInferenciaTableau()
        self.formulas = []
        self.ramas = []
        self.tam_fuente = 10

        raiz.title("Motor de inferencia - Tableau analítico")
        raiz.geometry("1300x800")
        raiz.minsize(1050, 650)
        raiz.configure(bg=BG)

        self.familia = tkfont.nametofont("TkDefaultFont").actual("family")
        self.fuente = tkfont.Font(family=self.familia, size=self.tam_fuente)
        self.fuente_b = tkfont.Font(family=self.familia, size=self.tam_fuente, weight="bold")

        self.crear_estilos()
        self.crear_menu()
        self.crear_interfaz()
        self.invalidar()

        # Guardado automático al cerrar la ventana
        self.raiz.protocol("WM_DELETE_WINDOW", self.al_cerrar)

        # Cargar archivo pasado por línea de comandos o restaurar sesión guardada
        cargado = False
        if len(sys.argv) > 1 and os.path.isfile(sys.argv[1]):
            cargado = self.cargar_desde_ruta(sys.argv[1], mostrar_mensaje=False)
        if not cargado:
            self.cargar_automatico()

    def crear_menu(self):
        menubar = tk.Menu(self.raiz)

        menu_archivo = tk.Menu(menubar, tearoff=0)
        menu_archivo.add_command(label="Nuevo (Limpiar)", command=self.limpiar, accelerator="Cmd+N")
        menu_archivo.add_command(label="Cargar archivo...", command=self.cargar_archivo, accelerator="Cmd+O")
        menu_archivo.add_command(label="Guardar reglas...", command=self.guardar_archivo, accelerator="Cmd+S")
        menu_archivo.add_separator()
        menu_archivo.add_command(label="Cargar ejemplo", command=self.cargar_ejemplo)
        menu_archivo.add_separator()
        menu_archivo.add_command(label="Salir", command=self.al_cerrar)
        menubar.add_cascade(label="Archivo", menu=menu_archivo)

        menu_eval = tk.Menu(menubar, tearoff=0)
        menu_eval.add_command(label="Evaluar con tableau", command=self.evaluar, accelerator="Cmd+R")
        menubar.add_cascade(label="Evaluar", menu=menu_eval)

        self.raiz.config(menu=menubar)

        # Atajos de teclado
        self.raiz.bind_all("<Command-o>", lambda e: self.cargar_archivo())
        self.raiz.bind_all("<Control-o>", lambda e: self.cargar_archivo())
        self.raiz.bind_all("<Command-s>", lambda e: self.guardar_archivo())
        self.raiz.bind_all("<Control-s>", lambda e: self.guardar_archivo())
        self.raiz.bind_all("<Command-n>", lambda e: self.limpiar())
        self.raiz.bind_all("<Control-n>", lambda e: self.limpiar())
        self.raiz.bind_all("<Command-r>", lambda e: self.evaluar())
        self.raiz.bind_all("<Control-r>", lambda e: self.evaluar())

    # ---------- construcción de la ventana ----------

    def crear_estilos(self):
        e = ttk.Style(self.raiz)
        e.theme_use("clam")
        e.configure("TFrame", background=BG)
        e.configure("TPanedwindow", background=BG)
        e.configure("TLabelframe", background=BG, bordercolor=BORDE)
        e.configure("TLabelframe.Label", background=BG, foreground=TEXTO, font=(self.familia, 10, "bold"))
        e.configure("TLabel", background=BG, foreground=TEXTO)
        e.configure("Suave.TLabel", background=BG, foreground=SUAVE)
        e.configure("Treeview", rowheight=24, background=PANEL, fieldbackground=PANEL,
                    foreground=TEXTO, bordercolor=BORDE)
        e.configure("Treeview.Heading", font=(self.familia, 9, "bold"), background="#e4e8ed", foreground=TEXTO)
        e.map("Treeview", background=[("selected", ACENTO_SUAVE)], foreground=[("selected", TEXTO)])
        e.configure("Acento.TButton", background=ACENTO, foreground="white",
                    font=(self.familia, 10, "bold"), padding=8)
        e.map("Acento.TButton", background=[("active", "#244a6e"), ("pressed", "#1d3b57")])

    def crear_interfaz(self):
        divisor = ttk.PanedWindow(self.raiz, orient="horizontal")
        divisor.pack(fill="both", expand=True, padx=10, pady=10)

        izq = ttk.Frame(divisor)
        der = ttk.PanedWindow(divisor, orient="vertical")
        divisor.add(izq, weight=2)
        divisor.add(der, weight=5)

        self.crear_reglas(izq)
        self.crear_atomos(izq)
        der.add(self.crear_arbol(der), weight=3)
        der.add(self.crear_resultado(der), weight=2)

    def crear_reglas(self, padre):
        marco = ttk.LabelFrame(padre, text="1. Base de conocimiento", padding=8)
        marco.pack(fill="both", expand=True)

        fila = ttk.Frame(marco)
        fila.pack(fill="x")
        self.entrada = ttk.Entry(fila)
        self.entrada.pack(side="left", fill="x", expand=True)
        self.entrada.bind("<Return>", self.agregar)
        ttk.Button(fila, text="Agregar", command=self.agregar).pack(side="left", padx=(6, 0))

        ttk.Label(marco, style="Suave.TLabel", wraplength=360, justify="left",
                  text="Conectores: si … entonces …, … si y solo si …, … o …, … y …, no …"
                  ).pack(anchor="w", pady=(4, 6))

        cuerpo = ttk.Frame(marco)
        cuerpo.pack(fill="both", expand=True)
        self.tabla_reglas = ttk.Treeview(cuerpo, columns=("n", "regla", "formula"),
                                         show="headings", height=7, selectmode="browse")
        for col, titulo, ancho in (("n", "R", 36), ("regla", "Regla", 190), ("formula", "Fórmula", 130)):
            self.tabla_reglas.heading(col, text=titulo)
            self.tabla_reglas.column(col, width=ancho, anchor="center" if col == "n" else "w",
                                     stretch=col != "n")
        barra = ttk.Scrollbar(cuerpo, orient="vertical", command=self.tabla_reglas.yview)
        self.tabla_reglas.configure(yscrollcommand=barra.set)
        self.tabla_reglas.pack(side="left", fill="both", expand=True)
        barra.pack(side="left", fill="y")

        botones = ttk.Frame(marco)
        botones.pack(fill="x", pady=(6, 0))
        ttk.Button(botones, text="Quitar", command=self.quitar).pack(side="left")
        ttk.Button(botones, text="Limpiar", command=self.limpiar).pack(side="left", padx=4)
        ttk.Button(botones, text="Ejemplo", command=self.cargar_ejemplo).pack(side="left")

        botones_arch = ttk.Frame(marco)
        botones_arch.pack(fill="x", pady=(5, 0))
        ttk.Button(botones_arch, text="📂 Cargar archivo", command=self.cargar_archivo).pack(side="left", fill="x", expand=True)
        ttk.Button(botones_arch, text="💾 Guardar archivo", command=self.guardar_archivo).pack(side="left", fill="x", expand=True, padx=(4, 0))

        ttk.Button(marco, text="Evaluar con tableau", style="Acento.TButton",
                   command=self.evaluar).pack(fill="x", pady=(8, 0))

    def crear_atomos(self, padre):
        marco = ttk.LabelFrame(padre, text="2. Tabla de átomos", padding=8)
        marco.pack(fill="both", expand=True, pady=(10, 0))
        self.tabla_atomos = ttk.Treeview(marco, columns=("atomo", "significado"),
                                         show="headings", height=6, selectmode="none")
        self.tabla_atomos.heading("atomo", text="Átomo")
        self.tabla_atomos.heading("significado", text="Significado")
        self.tabla_atomos.column("atomo", width=60, anchor="center", stretch=False)
        self.tabla_atomos.column("significado", width=300, anchor="w")
        barra = ttk.Scrollbar(marco, orient="vertical", command=self.tabla_atomos.yview)
        self.tabla_atomos.configure(yscrollcommand=barra.set)
        self.tabla_atomos.pack(side="left", fill="both", expand=True)
        barra.pack(side="left", fill="y")

    def crear_arbol(self, padre):
        marco = ttk.LabelFrame(padre, text="3. Árbol semántico (tableau)", padding=8)

        barra = ttk.Frame(marco)
        barra.pack(fill="x", pady=(0, 6))
        for texto, fondo, color in (("Rama abierta ✓", OK_FONDO, OK),
                                    ("Rama cerrada ✕", MAL_FONDO, MAL),
                                    ("Nodo intermedio", MEDIO_FONDO, MEDIO)):
            tk.Label(barra, text=texto, bg=fondo, fg=color, padx=8, pady=2).pack(side="left", padx=(0, 6))
        ttk.Button(barra, text="A+", width=4, command=lambda: self.zoom(1)).pack(side="right")
        ttk.Button(barra, text="A−", width=4, command=lambda: self.zoom(-1)).pack(side="right", padx=(0, 4))
        ttk.Label(barra, text="Arrastra para mover el árbol", style="Suave.TLabel").pack(side="right", padx=8)

        cuerpo = ttk.Frame(marco)
        cuerpo.pack(fill="both", expand=True)
        cuerpo.rowconfigure(0, weight=1)
        cuerpo.columnconfigure(0, weight=1)
        self.lienzo = tk.Canvas(cuerpo, bg=PANEL, highlightthickness=1, highlightbackground=BORDE)
        sb_v = ttk.Scrollbar(cuerpo, orient="vertical", command=self.lienzo.yview)
        sb_h = ttk.Scrollbar(cuerpo, orient="horizontal", command=self.lienzo.xview)
        self.lienzo.configure(yscrollcommand=sb_v.set, xscrollcommand=sb_h.set)
        self.lienzo.grid(row=0, column=0, sticky="nsew")
        sb_v.grid(row=0, column=1, sticky="ns")
        sb_h.grid(row=1, column=0, sticky="ew")

        self.lienzo.bind("<ButtonPress-1>", lambda e: self.lienzo.scan_mark(e.x, e.y))
        self.lienzo.bind("<B1-Motion>", lambda e: self.lienzo.scan_dragto(e.x, e.y, gain=1))
        for evento in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            self.lienzo.bind(evento, self.rueda)
        return marco

    def crear_resultado(self, padre):
        marco = ttk.LabelFrame(padre, text="4. Resultado global", padding=8)

        self.banner = tk.Label(marco, anchor="w", justify="left", padx=12, pady=8,
                               font=(self.familia, 11, "bold"))
        self.banner.pack(fill="x")
        self.banner.bind("<Configure>", lambda e: self.banner.configure(wraplength=max(e.width - 24, 100)))

        self.estadisticas = ttk.Label(marco, style="Suave.TLabel")
        self.estadisticas.pack(anchor="w", pady=4)

        cuerpo = ttk.Frame(marco)
        cuerpo.pack(fill="both", expand=True)
        self.tabla_resultado = ttk.Treeview(cuerpo, columns=("significado", "valor"),
                                            show="tree headings", height=6, selectmode="none")
        self.tabla_resultado.heading("#0", text="Rama / átomo")
        self.tabla_resultado.heading("significado", text="Significado")
        self.tabla_resultado.heading("valor", text="Valor")
        self.tabla_resultado.column("#0", width=150, stretch=False)
        self.tabla_resultado.column("significado", width=260)
        self.tabla_resultado.column("valor", width=130, stretch=False)
        self.tabla_resultado.tag_configure("abierta", foreground=OK)
        self.tabla_resultado.tag_configure("cerrada", foreground=MAL)
        self.tabla_resultado.tag_configure("verdadero", foreground=OK)
        self.tabla_resultado.tag_configure("falso", foreground=MAL)
        barra = ttk.Scrollbar(cuerpo, orient="vertical", command=self.tabla_resultado.yview)
        self.tabla_resultado.configure(yscrollcommand=barra.set)
        self.tabla_resultado.pack(side="left", fill="both", expand=True)
        barra.pack(side="left", fill="y")
        return marco

    # ---------- reglas y átomos ----------

    def analizar(self, reglas):
        motor = MotorInferenciaTableau()
        return motor, [motor.parsear_proposicion(r) for r in reglas]

    def agregar(self, _evento=None):
        texto = self.entrada.get().strip()
        if not texto:
            return
        try:
            motor, formulas = self.analizar(self.reglas + [texto])
        except Exception as error:
            messagebox.showerror("Regla no válida", str(error))
            return
        self.reglas.append(texto)
        self.entrada.delete(0, "end")
        self.actualizar(motor, formulas)

    def quitar(self):
        seleccion = self.tabla_reglas.selection()
        if not seleccion:
            return
        self.reglas.pop(int(seleccion[0]))
        self.actualizar(*self.analizar(self.reglas))

    def limpiar(self):
        self.reglas = []
        self.actualizar(*self.analizar(self.reglas))

    def cargar_ejemplo(self):
        self.reglas = list(EJEMPLO)
        self.actualizar(*self.analizar(self.reglas))

    def actualizar(self, motor, formulas, guardar=True):
        self.motor, self.formulas = motor, formulas
        self.tabla_reglas.delete(*self.tabla_reglas.get_children())
        for i, (texto, f) in enumerate(zip(self.reglas, formulas), 1):
            self.tabla_reglas.insert("", "end", iid=str(i - 1),
                                     values=(f"R{i}", texto, motor.formula_a_string(f)))
        self.tabla_atomos.delete(*self.tabla_atomos.get_children())
        for letra, significado in sorted(motor.inverso_atomos.items()):
            self.tabla_atomos.insert("", "end", values=(letra, significado))
        self.invalidar()
        if guardar:
            self.guardar_automatico()

    # ---------- persistencia (guardar y cargar) ----------

    def al_cerrar(self):
        """Se ejecuta al cerrar la ventana para garantizar que los datos queden guardados."""
        self.guardar_automatico()
        self.raiz.destroy()

    def guardar_automatico(self):
        """Guarda automáticamente la base de conocimiento actual en el archivo de persistencia."""
        try:
            datos = {
                "version": 1,
                "actualizado": datetime.now().isoformat(),
                "total_reglas": len(self.reglas),
                "reglas": self.reglas
            }
            with open(ARCHIVO_PERSISTENCIA, "w", encoding="utf-8") as f:
                json.dump(datos, f, ensure_ascii=False, indent=2)
        except Exception as e:
            print(f"Error al guardar persistencia automática: {e}", file=sys.stderr)

    def cargar_automatico(self):
        """Carga la base de conocimiento guardada en la última sesión si existe."""
        if not os.path.exists(ARCHIVO_PERSISTENCIA):
            return False
        try:
            with open(ARCHIVO_PERSISTENCIA, "r", encoding="utf-8") as f:
                datos = json.load(f)
            reglas = datos.get("reglas", [])
            if reglas and isinstance(reglas, list):
                motor, formulas = self.analizar(reglas)
                self.reglas = reglas
                self.actualizar(motor, formulas, guardar=False)
                return True
        except Exception as e:
            print(f"No se pudo cargar persistencia previa: {e}", file=sys.stderr)
        return False

    def leer_reglas_de_archivo(self, ruta):
        """Lee un archivo (.json o .txt) y retorna una lista de reglas limpias."""
        if not os.path.isfile(ruta):
            raise FileNotFoundError(f"El archivo no existe: {ruta}")

        _, ext = os.path.splitext(ruta.lower())
        contenido_texto = None
        for enc in ("utf-8", "utf-8-sig", "latin-1"):
            try:
                with open(ruta, "r", encoding=enc) as f:
                    contenido_texto = f.read()
                break
            except UnicodeDecodeError:
                continue

        if contenido_texto is None:
            raise ValueError("No se pudo descodificar el archivo. Asegúrate de que use codificación UTF-8.")

        reglas = []
        if ext == ".json":
            datos = json.loads(contenido_texto)
            if isinstance(datos, dict):
                reglas = datos.get("reglas", [])
            elif isinstance(datos, list):
                reglas = datos
            else:
                raise ValueError("El archivo JSON debe contener una lista de reglas o un objeto con la clave 'reglas'.")
        else:
            for linea in contenido_texto.splitlines():
                l = linea.strip()
                if l and not l.startswith("#"):
                    reglas.append(l)

        return [str(r).strip() for r in reglas if str(r).strip()]

    def cargar_desde_ruta(self, ruta, mostrar_mensaje=True):
        """Carga reglas desde una ruta de archivo, validando sintaxis y actualizando la interfaz."""
        try:
            reglas_nuevas = self.leer_reglas_de_archivo(ruta)
            if not reglas_nuevas:
                if mostrar_mensaje:
                    messagebox.showwarning("Archivo vacío", "El archivo seleccionado no contiene reglas.")
                return False

            # Validar regla por regla para reportar error específico si falla la sintaxis
            for idx, regla in enumerate(reglas_nuevas, 1):
                try:
                    motor_test = MotorInferenciaTableau()
                    motor_test.parsear_proposicion(regla)
                except Exception as err_sintaxis:
                    raise ValueError(f"Regla #{idx} ('{regla}'): {err_sintaxis}")

            motor, formulas = self.analizar(reglas_nuevas)
            self.reglas = reglas_nuevas
            self.actualizar(motor, formulas, guardar=True)
            if mostrar_mensaje:
                messagebox.showinfo(
                    "Carga exitosa",
                    f"Se cargaron correctamente {len(reglas_nuevas)} reglas desde:\n{os.path.basename(ruta)}"
                )
            return True
        except Exception as e:
            if mostrar_mensaje:
                messagebox.showerror("Error al cargar archivo", f"No se pudo cargar el archivo:\n{e}")
            return False

    def cargar_archivo(self):
        """Abre un cuadro de diálogo para seleccionar y cargar un archivo guardado."""
        ruta = filedialog.askopenfilename(
            title="Cargar archivo de reglas",
            filetypes=[
                ("Archivos compatibles (*.json, *.txt)", "*.json *.txt"),
                ("Archivos JSON (*.json)", "*.json"),
                ("Archivos de texto (*.txt)", "*.txt"),
                ("Todos los archivos", "*.*")
            ]
        )
        if ruta:
            self.cargar_desde_ruta(ruta, mostrar_mensaje=True)

    def guardar_archivo(self):
        """Abre un cuadro de diálogo para guardar las reglas actuales a un archivo JSON o TXT."""
        if not self.reglas:
            messagebox.showinfo("Sin reglas", "No hay reglas en la base de conocimiento para guardar.")
            return

        ruta = filedialog.asksaveasfilename(
            title="Guardar reglas",
            defaultextension=".json",
            filetypes=[
                ("Archivo JSON (*.json)", "*.json"),
                ("Archivo de texto (*.txt)", "*.txt"),
                ("Todos los archivos", "*.*")
            ]
        )
        if not ruta:
            return

        try:
            _, ext = os.path.splitext(ruta.lower())
            if ext == ".txt":
                with open(ruta, "w", encoding="utf-8") as f:
                    for r in self.reglas:
                        f.write(f"{r}\n")
            else:
                datos = {
                    "version": 1,
                    "fecha": datetime.now().isoformat(),
                    "total_reglas": len(self.reglas),
                    "reglas": self.reglas
                }
                with open(ruta, "w", encoding="utf-8") as f:
                    json.dump(datos, f, ensure_ascii=False, indent=2)

            messagebox.showinfo(
                "Guardado exitoso",
                f"Se guardaron {len(self.reglas)} reglas en:\n{os.path.basename(ruta)}"
            )
        except Exception as e:
            messagebox.showerror("Error al guardar", f"No se pudo guardar el archivo:\n{e}")

    def invalidar(self):
        self.ramas = []
        self.dibujar_arbol()
        self.tabla_resultado.delete(*self.tabla_resultado.get_children())
        self.banner.configure(text="Sin evaluar. Agrega reglas y pulsa «Evaluar con tableau».",
                              bg=MEDIO_FONDO, fg=MEDIO)
        self.estadisticas.configure(text="")

    # ---------- evaluación ----------

    def evaluar(self):
        if not self.reglas:
            messagebox.showinfo("Sin reglas", "Agrega al menos una regla antes de evaluar.")
            return
        ramas = resolver_tableau(self.formulas)
        for r in ramas:
            r['closed'] = branch_es_contradictoria(r['formulas'])
        self.ramas = ramas
        self.dibujar_arbol()
        self.mostrar_resultados()

    def modelo_de_rama(self, r):
        asignaciones = {atomo: "Falso (F)" for atomo in self.motor.inverso_atomos.keys()}
        for f in r['formulas']:
            if f[0] == 'atom':
                asignaciones[f[1]] = "Verdadero (V)"
            elif f[0] == 'not' and f[1][0] == 'atom':
                asignaciones[f[1][1]] = "Falso (F)"
        return asignaciones

    def mostrar_resultados(self):
        abiertas = [r for r in self.ramas if not r['closed']]
        if abiertas:
            texto = "La base de conocimiento es CONSISTENTE. Se encontraron modelos válidos donde todas las reglas se cumplen."
            fondo, color = OK_FONDO, OK
        else:
            texto = "La base de conocimiento es INCONSISTENTE (todas las ramas se cierran ✕)."
            fondo, color = MAL_FONDO, MAL
        self.banner.configure(text=texto, bg=fondo, fg=color)
        self.estadisticas.configure(
            text=f"{len(self.ramas)} ramas: {len(abiertas)} abiertas, {len(self.ramas) - len(abiertas)} cerradas")

        tabla = self.tabla_resultado
        tabla.delete(*tabla.get_children())
        for r in sorted(self.ramas, key=lambda r: r['id'].split('.')):
            if r['closed']:
                contra = ", ".join(f"{a} y ¬{a}" for a in atomos_contradictorios(r['formulas']))
                tabla.insert("", "end", text=f"Rama {r['id']}",
                             values=(f"contradicción: {contra}", "CERRADA ✕"), tags=("cerrada",))
            else:
                fila = tabla.insert("", "end", text=f"Rama {r['id']}",
                                    values=("modelo", "ABIERTA ✓"), tags=("abierta",), open=True)
                for atomo, valor in sorted(self.modelo_de_rama(r).items()):
                    etiqueta = "verdadero" if valor.startswith("Verdadero") else "falso"
                    tabla.insert(fila, "end", text=atomo,
                                 values=(self.motor.inverso_atomos[atomo], valor), tags=(etiqueta,))

    # ---------- dibujo del árbol ----------

    def zoom(self, paso):
        nuevo = min(max(self.tam_fuente + paso, 7), 18)
        if nuevo != self.tam_fuente:
            self.tam_fuente = nuevo
            self.fuente.configure(size=nuevo)
            self.fuente_b.configure(size=nuevo)
            if self.ramas:
                self.dibujar_arbol()

    def rueda(self, e):
        sentido = -1 if (e.num == 4 or e.delta > 0) else 1
        if e.state & 0x1:
            self.lienzo.xview_scroll(sentido, "units")
        else:
            self.lienzo.yview_scroll(sentido, "units")

    def preparar_nodo(self, n):
        rama = n['rama']
        if rama is None:
            estilo, titulo = (MEDIO, MEDIO_FONDO), f"Rama {n['id']}"
        elif rama['closed']:
            estilo, titulo = (MAL, MAL_FONDO), f"Rama {n['id']}  ✕ cerrada"
        else:
            estilo, titulo = (OK, OK_FONDO), f"Rama {n['id']}  ✓ abierta"

        lineas = []
        for i, f in enumerate(n['acum'][n['previo']:], n['previo']):
            prefijo = f"R{i + 1}: " if i < len(self.formulas) else ""
            lineas.append((prefijo + self.motor.formula_a_string(f), TEXTO))
        if rama is not None:
            if rama['closed']:
                contra = ", ".join(f"{a} y ¬{a}" for a in atomos_contradictorios(rama['formulas']))
                lineas.append((f"✕ contradicción: {contra}", MAL))
            else:
                lineas.append(("✓ modelo encontrado", OK))

        paso = self.fuente.metrics("linespace")
        ancho_texto = max([self.fuente_b.measure(titulo)] + [self.fuente.measure(t) for t, _ in lineas])
        n['estilo'], n['titulo'], n['lineas'], n['paso'] = estilo, titulo, lineas, paso
        n['alto_cab'] = paso + 2 * PAD_CAB
        n['w'] = ancho_texto + 2 * PAD_X
        n['h'] = n['alto_cab'] + (len(lineas) * paso + 2 * PAD_Y if lineas else 0)

    def dibujar_arbol(self):
        lienzo = self.lienzo
        lienzo.delete("all")
        if not self.ramas:
            lienzo.create_text(20, 20, anchor="nw", fill=SUAVE, font=self.fuente,
                               text="Agrega reglas y pulsa «Evaluar con tableau» para ver el árbol.")
            lienzo.configure(scrollregion=(0, 0, 0, 0))
            return

        raiz = construir_arbol(self.ramas)
        nodos = recorrer(raiz)
        for n in nodos:
            self.preparar_nodo(n)
        disponer(raiz, SEP_X, SEP_Y, x0=max((lienzo.winfo_width() - raiz['w']) / 2, 20))

        for n in nodos:
            for h in n['hijos']:
                lienzo.create_line(n['cx'], n['y'] + n['h'], h['cx'], h['y'], fill=LINEA, width=2)
        for n in nodos:
            color, fondo = n['estilo']
            x0, x1 = n['cx'] - n['w'] / 2, n['cx'] + n['w'] / 2
            y0 = n['y']
            lienzo.create_rectangle(x0, y0, x1, y0 + n['h'], fill=fondo, outline=color, width=2)
            lienzo.create_rectangle(x0, y0, x1, y0 + n['alto_cab'], fill=color, outline=color)
            lienzo.create_text(x0 + PAD_X, y0 + n['alto_cab'] / 2, anchor="w",
                               text=n['titulo'], fill="white", font=self.fuente_b)
            y = y0 + n['alto_cab'] + PAD_Y
            for texto, col in n['lineas']:
                lienzo.create_text(x0 + PAD_X, y, anchor="nw", text=texto, fill=col, font=self.fuente)
                y += n['paso']

        caja = lienzo.bbox("all")
        lienzo.configure(scrollregion=(caja[0] - 20, caja[1] - 20, caja[2] + 20, caja[3] + 20))
        lienzo.xview_moveto(0)
        lienzo.yview_moveto(0)


if __name__ == "__main__":
    try:
        from ctypes import windll
        windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass
    ventana = tk.Tk()
    App(ventana)
    ventana.mainloop()