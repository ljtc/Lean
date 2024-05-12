# Lean
Repositorio para compartir los avances que hagamos en el aprendizaje de Lean.
Para aprender lo básico de la sintaxis estaremos leyendo y haciendo los
ejercicios de *Proof Theory* de Gaisi Takeuti


## Instalación

1. Instalar [VS Code](https://code.visualstudio.com/)
2. Buscar e instalar [lean4] (https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) en las extensiones de VS Code
3. Después de instalar `lean4` se abrirá una guía *Lean 4 Setup*. Para acceder a esa guía se puede dar click en el símbolo ∀ de arriba a la derecha, luego en *Documentation* > *Setup: Show Setup Guide*.
4. Hay que hacer lo que dice la guía. Sobretodo el paso que dice *Install Required Dependencies* y el siguiente, *Install Lean Version Manager*.
5. Para usar la biblioteca de matemáticas es suficiente dar clic en el símbolo ∀ y luego *New Project* > *Project: Create Project Using Mathlib*

Como es buena idea leer  *Mathematics in Lean*, se recomienda bajar el libro ya que contiene archivos con ejemplos y ejercicios.

```
git clone https://github.com/leanprover-community/mathematics_in_lean.git
cd mathematics_in_lean
lake exe cache get
```

Con esas tres instrucciones se creará una carpeta `mathematics_in_lean` dentro de ella habrá otra llamada `MIL`. Esta es la carpeta con los ejemplos y ejercicios. No se debe trabajar directamente en ella. Se debe hacer una copia y trabajar sobre la copia.

Todos los archivos importan una biblioteca especial
```
import MIL.Common
```
Esta biblioteca, que parece ser para el libro, sólo causa errores así que hay
que eliminar esa línea


## Tarea

[] Hacer los ejercicios de `TLP.lean`