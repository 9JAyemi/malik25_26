// SVA checker for multiplexer_system
// Concise, full functional equivalence + key internal invariants + coverage
module multiplexer_system_sva (
  input  logic [2:0] sel,
  input  logic [3:0] data0, data1, data2, data3, data4, data5,
  input  logic [3:0] out,
  // bind these internal signals explicitly
  input  logic [3:0] mux1_out,
  input  logic [3:0] and_out
);

  // Sample on any combinational activity
  default clocking cb @(*); endclocking

  function automatic logic and_lsb12 (
    input logic [3:0] d0,d1,d2,d3,d4,d5
  );
    and_lsb12 = &{d5[1:0],d4[1:0],d3[1:0],d2[1:0],d1[1:0],d0[1:0]};
  endfunction

  // End-to-end functional equivalence for out
  assert property (
    1 |-> out ==
      ( (sel[2:1]==2'b11) ? {3'b000, and_lsb12(data0,data1,data2,data3,data4,data5)} :
        (sel==3'b000) ? data0 :
        (sel==3'b001) ? data1 :
        (sel==3'b010) ? data2 :
        (sel==3'b011) ? data3 :
        (sel==3'b100) ? data4 :
        (sel==3'b101) ? data5 : 4'b000 )
  );

  // Internal path invariants
  // mux1_out correctness for 000..101 and default 6/7 -> 0
  assert property ( (sel==3'b000) |-> mux1_out==data0 );
  assert property ( (sel==3'b001) |-> mux1_out==data1 );
  assert property ( (sel==3'b010) |-> mux1_out==data2 );
  assert property ( (sel==3'b011) |-> mux1_out==data3 );
  assert property ( (sel==3'b100) |-> mux1_out==data4 );
  assert property ( (sel==3'b101) |-> mux1_out==data5 );
  assert property ( (sel inside {3'b110,3'b111}) |-> mux1_out==4'b000 );

  // and_out is only used for 110/111 and equals reduction of 12 LSBs (in LSB)
  assert property ( (sel inside {3'b110,3'b111}) |-> and_out == {3'b000, and_lsb12(data0,data1,data2,data3,data4,data5)} );
  assert property ( !(sel inside {3'b110,3'b111}) |-> and_out==4'b000 );

  // Final selector stage correctness
  assert property ( (sel inside {3'b110,3'b111}) |-> out==and_out );
  assert property ( !(sel inside {3'b110,3'b111}) |-> out==mux1_out );

  // X-propagation guard: clean inputs imply clean internals/outputs
  assert property ( !$isunknown({sel,data0,data1,data2,data3,data4,data5})
                    |-> !$isunknown({mux1_out,and_out,out}) );

  // Coverage: hit each select; hit both AND outcomes
  cover property ( sel==3'b000 && out==data0 );
  cover property ( sel==3'b001 && out==data1 );
  cover property ( sel==3'b010 && out==data2 );
  cover property ( sel==3'b011 && out==data3 );
  cover property ( sel==3'b100 && out==data4 );
  cover property ( sel==3'b101 && out==data5 );
  cover property ( sel inside {3'b110,3'b111} && and_out==4'b0001 && out==and_out );
  cover property ( sel inside {3'b110,3'b111} && and_out==4'b0000 && out==and_out );

endmodule

// Bind into the DUT; note explicit connections to internal regs mux1_out/and_out
bind multiplexer_system multiplexer_system_sva sva_i (
  .sel(sel),
  .data0(data0), .data1(data1), .data2(data2), .data3(data3), .data4(data4), .data5(data5),
  .out(out),
  .mux1_out(mux1_out),
  .and_out(and_out)
);