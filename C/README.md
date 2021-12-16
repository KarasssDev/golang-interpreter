### An implementaion of C mini-language

This is a homework for functional programming course.

License: LGPL for implementation code + WTFPL for test examles in miniLanguage

Author: Andrew Oleynikob, a.oleyn1kov@outlook.com

Features done (append only):

- Ast,
- Parser,
- Interpreter,
- Tests.

Features in progress (and TODOs):

- Editing.

Замечания:

- Не поддерживается:
  - Указатели на функции
  - Изменение значений большего типа меньшим
    ```
    int* arr = malloc(sizeof(int));
    *arr = 1000000000;
    char *pt = arr;
    *pt = 'y'; 
    ```
    => 
    ```
    arr[0] == 121;
    ```
  - Запись вида:
    ```
    (*strct).arg0
    ``` 
    -- только стрелки,
  - Явное приведение типов,
  - Многомерные массивы (не указатели),
  - Строки,
  - Работа с битами,
  - Префиксный инкремент и декремент,
- Запись x++ или x-- эквивалентна x = x + 1 или x = x - 1,
- Объявление структур имеет вид:
    ```
    struct my_strct = {arg1, arg2};
    ```
- Типы структур приводятся, если они имеют одинаковые размеры и колличество полей, иначе неопределенное поведение в первом случае и ошибка во втором.