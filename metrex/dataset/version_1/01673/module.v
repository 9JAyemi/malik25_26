


module MISTRAL_ALUT6(input A, B, C, D, E, F, output Q);

parameter [63:0] LUT = 64'h0000_0000_0000_0000;

`ifdef cyclonev
specify
    (A => Q) = 605;
    (B => Q) = 583;
    (C => Q) = 510;
    (D => Q) = 512;
    (E => Q) = 400;
    (F => Q) = 97;
endspecify
`endif
`ifdef cyclone10gx
specify
    (A => Q) = 275;
    (B => Q) = 272;
    (C => Q) = 175;
    (D => Q) = 165;
    (E => Q) = 162;
    (F => Q) = 53;
endspecify
`endif

assign Q = LUT >> {F, E, D, C, B, A};

endmodule



module MISTRAL_ALUT5(input A, B, C, D, E, output Q);

parameter [31:0] LUT = 32'h0000_0000;

`ifdef cyclonev
specify
    (A => Q) = 583;
    (B => Q) = 510;
    (C => Q) = 512;
    (D => Q) = 400;
    (E => Q) = 97;
endspecify
`endif
`ifdef cyclone10gx
specify
    (A => Q) = 272;
    (B => Q) = 175;
    (C => Q) = 165;
    (D => Q) = 162;
    (E => Q) = 53;
endspecify
`endif

assign Q = LUT >> {E, D, C, B, A};

endmodule



module MISTRAL_ALUT4(input A, B, C, D, output Q);

parameter [15:0] LUT = 16'h0000;

`ifdef cyclonev
specify
    (A => Q) = 510;
    (B => Q) = 512;
    (C => Q) = 400;
    (D => Q) = 97;
endspecify
`endif
`ifdef cyclone10gx
specify
    (A => Q) = 175;
    (B => Q) = 165;
    (C => Q) = 162;
    (D => Q) = 53;
endspecify
`endif

assign Q = LUT >> {D, C, B, A};

endmodule



module MISTRAL_ALUT3(input A, B, C, output Q);

parameter [7:0] LUT = 8'h00;

`ifdef cyclonev
specify
    (A => Q) = 510;
    (B => Q) = 400;
    (C => Q) = 97;
endspecify
`endif
`ifdef cyclone10gx
specify
    (A => Q) = 165;
    (B => Q) = 162;
    (C => Q) = 53;
endspecify
`endif

assign Q = LUT >> {C, B, A};

endmodule



module MISTRAL_ALUT2(input A, B, output Q);

parameter [3:0] LUT = 4'h0;

`ifdef cyclonev
specify
    (A => Q) = 400;
    (B => Q) = 97;
endspecify
`endif
`ifdef cyclone10gx
specify
    (A => Q) = 162;
    (B => Q) = 53;
endspecify
`endif

assign Q = LUT >> {B, A};

endmodule



module MISTRAL_NOT(input A, output Q);

`ifdef cyclonev
specify
    (A => Q) = 97;
endspecify
`endif
`ifdef cyclone10gx
specify
    (A => Q) = 53;
endspecify
`endif

assign Q = ~A;

endmodule


module MISTRAL_ALUT_ARITH(input A, B, C, D0, D1,  input CI, output SO,  output CO);

parameter LUT0 = 16'h0000;
parameter LUT1 = 16'h0000;

`ifdef cyclonev
specify
    (A  => SO) = 1342;
    (B  => SO) = 1323;
    (C  => SO) = 927;
    (D0 => SO) = 887;
    (D1 => SO) = 785;
    (CI => SO) = 368;

    (A  => CO) = 1082;
    (B  => CO) = 1062;
    (C  => CO) = 813;
    (D0 => CO) = 866;
    (D1 => CO) = 1198;
    (CI => CO) = 36; endspecify
`endif
`ifdef cyclone10gx
specify
    (A  => SO) = 644;
    (B  => SO) = 477;
    (C  => SO) = 416;
    (D0 => SO) = 380;
    (D1 => SO) = 431;
    (CI => SO) = 276;

    (A  => CO) = 525;
    (B  => CO) = 433;
    (C  => CO) = 712;
    (D0 => CO) = 653;
    (D1 => CO) = 593;
    (CI => CO) = 16;
endspecify
`endif

wire q0, q1;

assign q0 = LUT0 >> {D0, C, B, A};
assign q1 = LUT1 >> {D1, C, B, A};

assign {CO, SO} = q0 + !q1 + CI;

endmodule



