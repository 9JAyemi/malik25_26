// SVA checker for priority_encoder
module priority_encoder_sva (
  input  logic        clk,   // sampling clock
  input  logic [3:0]  in,
  input  logic [1:0]  out
);
  default clocking cb @(posedge clk); endclocking

  function automatic logic [1:0] pri_idx (input logic [3:0] a);
    if (a[3]) return 2'd3;
    else if (a[2]) return 2'd2;
    else if (a[1]) return 2'd1;
    else           return 2'd0;
  endfunction

  // Functional equivalence (when any input bit is 1, out matches highest set index and is 2-state)
  a_func: assert property ( (|in) |-> ##0 (!$isunknown(out) && out == pri_idx(in)) );

  // When no inputs are set, out must be unknown (matches 2'bxx coding)
  a_none_x: assert property ( (in == 4'b0000) |-> ##0 $isunknown(out) );

  // Out must never be unknown when any input is set
  a_no_x_when_some: assert property ( (|in) |-> ##0 !$isunknown(out) );

  // Optional decode-side sanity (redundant with a_func but tightens intent)
  a_dec_11: assert property ( (out == 2'b11) |-> ##0 in[3] );
  a_dec_10: assert property ( (out == 2'b10) |-> ##0 (!in[3] && in[2]) );
  a_dec_01: assert property ( (out == 2'b01) |-> ##0 (!in[3] && !in[2] && in[1]) );
  a_dec_00: assert property ( (out == 2'b00) |-> ##0 (!in[3] && !in[2] && !in[1] && in[0]) );

  // Coverage: none-set, single-bit cases, and a few multi-hot priority cases
  c_none:  cover property ( (in == 4'b0000) && $isunknown(out) );
  c_0:     cover property ( (in == 4'b0001) && (out == 2'b00) );
  c_1:     cover property ( (in == 4'b0010) && (out == 2'b01) );
  c_2:     cover property ( (in == 4'b0100) && (out == 2'b10) );
  c_3:     cover property ( (in == 4'b1000) && (out == 2'b11) );
  c_mh1:   cover property ( (in == 4'b0011) && (out == 2'b01) ); // lower two set -> 1 has priority
  c_mh2:   cover property ( (in == 4'b0111) && (out == 2'b10) ); // 2 wins over 1/0
  c_mh3:   cover property ( (in == 4'b1011) && (out == 2'b11) ); // 3 wins over others
endmodule

// Example bind (ensure a suitable clock is in scope when binding):
// bind priority_encoder priority_encoder_sva u_pri_enc_sva(.clk(clk), .in(in), .out(out));