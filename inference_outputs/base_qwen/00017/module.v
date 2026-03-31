
module section2_schematic (n63, Z_B, n62, Len_int, Ren_int);
    input n63;
    input Z_B;
    input n62;
    output Len_int;
    output Ren_int;

    wire N_1;
    wire N_3;
    wire Ldir_int;
    wire Rdir_int;
    wire N_8;
    wire N_4;

    // Declare gates
    and (N_1, n63, Z_B);
    and (N_3, Z_B, n62);
    and (N_4, Ldir_int, N_8, Rdir_int);
    or (Len_int, N_1, N_4);
    or (Ren_int, N_4, N_3);
    not (Rdir_int, n62);
    not (Ldir_int, n63);
    not (N_8, Z_B);

endmodule
