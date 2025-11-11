// SVA checker for priority_encoder
// Bind this to the DUT. Focuses on functional correctness, priority behavior,
// absence of illegal cases, and coverage of each priority path.

module priority_encoder_sva (
  input  logic        clk,
  input  logic        rst_n,
  // DUT ports
  input  logic [7:0]  in,
  input  logic [2:0]  pos,
  // Internal DUT net
  input  logic [7:0]  gray_out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic sanity
  assert property (!$isunknown({in,pos,gray_out})))
    else $error("X/Z detected on inputs/outputs");

  // Reset/zero input behavior
  assert property (in == 8'b0 |-> (pos == 3'd0 && gray_out == 8'b0))
    else $error("Zero-input behavior violated");

  // Illegal case: in != 0 must not produce gray_out == 0 (flags design bug/latch hole)
  assert property (in != 8'b0 |-> gray_out != 8'b0)
    else $error("Nonzero input produced zero gray_out (illegal)");

  // Priority correctness for nonzero gray_out
  assert property ( (in != 8'b0 && gray_out != 8'b0)
                    |-> pos == (gray_out[7] ? 3'd7 :
                                gray_out[6] ? 3'd6 :
                                gray_out[5] ? 3'd5 :
                                gray_out[4] ? 3'd4 :
                                gray_out[3] ? 3'd3 :
                                gray_out[2] ? 3'd2 :
                                gray_out[1] ? 3'd1 :
                                              3'd0) )
    else $error("Priority mapping incorrect");

  // Per-level priority assertions (also help with targeted debug)
  assert property ( (in!=0 && gray_out[7])                           |-> pos==3'd7);
  assert property ( (in!=0 && !gray_out[7] && gray_out[6])           |-> pos==3'd6);
  assert property ( (in!=0 && !|gray_out[7:6] && gray_out[5])        |-> pos==3'd5);
  assert property ( (in!=0 && !|gray_out[7:5] && gray_out[4])        |-> pos==3'd4);
  assert property ( (in!=0 && !|gray_out[7:4] && gray_out[3])        |-> pos==3'd3);
  assert property ( (in!=0 && !|gray_out[7:3] && gray_out[2])        |-> pos==3'd2);
  assert property ( (in!=0 && !|gray_out[7:2] && gray_out[1])        |-> pos==3'd1);
  assert property ( (in!=0 && !|gray_out[7:1] && gray_out[0])        |-> pos==3'd0);

  // Functional coverage
  cover property (in == 8'b0);
  cover property (in != 8'b0 && gray_out == 8'b0); // hits the illegal corner (exposes bug)
  cover property (in!=0 && gray_out[7]                           && pos==3'd7);
  cover property (in!=0 && !gray_out[7] && gray_out[6]           && pos==3'd6);
  cover property (in!=0 && !|gray_out[7:6] && gray_out[5]        && pos==3'd5);
  cover property (in!=0 && !|gray_out[7:5] && gray_out[4]        && pos==3'd4);
  cover property (in!=0 && !|gray_out[7:4] && gray_out[3]        && pos==3'd3);
  cover property (in!=0 && !|gray_out[7:3] && gray_out[2]        && pos==3'd2);
  cover property (in!=0 && !|gray_out[7:2] && gray_out[1]        && pos==3'd1);
  cover property (in!=0 && !|gray_out[7:1] && gray_out[0]        && pos==3'd0);

endmodule

// Example bind (from testbench/top-level):
// bind priority_encoder priority_encoder_sva pe_sva (
//   .clk(tb_clk),
//   .rst_n(tb_rst_n),
//   .in(in),
//   .pos(pos),
//   .gray_out(gray_out) // internal net of DUT
// );