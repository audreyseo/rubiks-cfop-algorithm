Numbering scheme (cube net):

```
         U1 U2 U3
         U4 U5 U6
         U7 U8 U9
L1 L2 L3 F1 F2 F3 R1 R2 R3
L4 L5 L6 F4 F5 F6 R4 R5 R6
L7 L8 L9 F7 F8 F9 R7 R8 R9
         D1 D2 D3
         D4 D5 D6
         D7 D8 D9
         B1 B2 B3
         B4 B5 B6
         B7 B8 B9
```

Algorithm for getting the initial Daisy, phrased with yellow = up:

While at least one of U2, U4, U6, U8 is not white:
* Rotate the cube along the U-D axis until the not-white sticker is in position U8.
* Perform d (down+center rotation) until a white sticker is in one of the following locations:
    * Case F2: Perform F U' R U.
    * Case F6: Perform U' R U.
    * Case R4: Perform F'
    * Case F8: Perform F' U' R U.
    * Case D2: Perform F^2.
* Post condition: If U2, U4, and/or U6 were originally white, they are still white. U8 is now white (having the piece from F2/F6/R4/F8/D2).