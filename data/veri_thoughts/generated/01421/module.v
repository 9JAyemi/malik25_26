module v9a2795 (
 input [2:0] vdee7c7,
 output vda577d,
 output v3f8943,
 output v64d863
);
 wire w0;
 wire w1;
 wire [0:2] w2;
 wire w3;
 assign v3f8943 = w0;
 assign v64d863 = w1;
 assign w2 = vdee7c7;
 assign vda577d = w3;
 v9a2795_v9a2a06 v9a2a06 (
  .o1(w0),
  .o0(w1),
  .i(w2),
  .o2(w3)
 );
endmodule

module v9a2795_v9a2a06 (
 output o0,
 output o1,
 input [0:2] i,
 output o2
);
 wire w0;
 wire w1;
 wire w2;
 wire w3;
 assign w0 = i[1] & i[2];
 assign w1 = i[0] & i[2];
 assign w2 = i[0] & i[1];
 assign o2 = w0 | w1 | w2;
 assign o0 = w0 ^ w2;
 assign o1 = w1 ^ w2;
endmodule