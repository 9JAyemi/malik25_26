// SVA for parity_generator and parity_byte
// Bind-ready, concise, checks correctness and provides focused coverage

// Checker for parity_generator: parity_out must be odd parity of data_in
module parity_generator_sva (
  input [7:0] data_in,
  input       parity_out
);
  // Comb correctness (fires on any change to inputs/outputs)
  a_parity_correct: assert property (@(data_in or parity_out)
    !$isunknown({data_in,parity_out}) |->
    (parity_out == ^data_in)
  );

  // Coverage
  c_parity0: cover property (@(data_in or parity_out) (^data_in==1'b0) && (parity_out==1'b0));
  c_parity1: cover property (@(data_in or parity_out) (^data_in==1'b1) && (parity_out==1'b1));
endmodule

// Checker for parity_byte: muxing and final byte composition
module parity_byte_sva (
  input         clk,
  input         reset,
  input  [7:0]  a,
  input  [7:0]  b,
  input         sel_b1,
  input         sel_b2,
  input  [8:0]  out_byte
);
  // Convenience expressions
  wire [7:0] exp_data = (sel_b1 && !sel_b2) ? a :
                        (!sel_b1 && sel_b2) ? b : 8'h00;

  // No X/Z on key signals at sampling time
  a_no_x: assert property (@(posedge clk) disable iff (reset)
    !$isunknown({sel_b1,sel_b2,a,b,out_byte})
  );

  // Lower 8 bits must equal selected data (or 0s when selects equal)
  a_mux_a: assert property (@(posedge clk) disable iff (reset)
    (sel_b1 && !sel_b2) |-> (out_byte[7:0] == a)
  );
  a_mux_b: assert property (@(posedge clk) disable iff (reset)
    (!sel_b1 && sel_b2) |-> (out_byte[7:0] == b)
  );
  a_mux_def: assert property (@(posedge clk) disable iff (reset)
    (sel_b1 === sel_b2) |-> (out_byte[7:0] == 8'h00)
  );

  // Parity bit must be odd parity of the data bits
  a_parity_bit: assert property (@(posedge clk) disable iff (reset)
    out_byte[8] == ^out_byte[7:0]
  );

  // Cross-coverage: exercise select cases and both parity types
  c_sel_a:    cover property (@(posedge clk) disable iff (reset)
    (sel_b1 && !sel_b2) && (out_byte[7:0] == a)
  );
  c_sel_b:    cover property (@(posedge clk) disable iff (reset)
    (!sel_b1 && sel_b2) && (out_byte[7:0] == b)
  );
  c_sel_00:   cover property (@(posedge clk) disable iff (reset)
    (!sel_b1 && !sel_b2) && (out_byte[7:0] == 8'h00)
  );
  c_sel_11:   cover property (@(posedge clk) disable iff (reset)
    ( sel_b1 &&  sel_b2) && (out_byte[7:0] == 8'h00)
  );
  c_par0:     cover property (@(posedge clk) disable iff (reset)
    (^out_byte[7:0] == 1'b0) && (out_byte[8] == 1'b0)
  );
  c_par1:     cover property (@(posedge clk) disable iff (reset)
    (^out_byte[7:0] == 1'b1) && (out_byte[8] == 1'b1)
  );
endmodule

// Bind to DUTs
bind parity_generator parity_generator_sva u_parity_generator_sva (.data_in(data_in), .parity_out(parity_out));
bind parity_byte      parity_byte_sva      u_parity_byte_sva      (.*);