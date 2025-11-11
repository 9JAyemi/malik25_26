// SVA for simple_encryption
module simple_encryption_sva (
  input logic        clk,
  input logic        rst,     // active-low async reset
  input logic [15:0] data_in,
  input logic [7:0]  key,
  input logic        encrypt,
  input logic [15:0] data_out,
  input logic [7:0]  A,
  input logic [7:0]  B,
  input logic [7:0]  temp
);

  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset drives A/B to 0 immediately on negedge
  a_async_reset_zero: assert property (@(negedge rst) ##0 (A==8'h00 && B==8'h00));

  // While in reset, A/B hold at 0 on every clk edge
  a_hold_zero_in_reset: assert property (@(posedge clk) !rst |-> (A==8'h00 && B==8'h00));

  // Register update semantics (last NBA to A/B/temp wins): rotation of previous values
  a_reg_rotation: assert property (disable iff (!rst)
    !$isunknown($past({A,B,temp})) |-> (A==$past(B) && B==$past(temp) && temp==$past(A))
  );

  // data_out is concatenation of previous A/B, order selected by encrypt
  a_dataout_map: assert property (disable iff (!rst)
    !$isunknown($past({A,B})) |-> data_out == (encrypt ? {$past(A),$past(B)} : {$past(B),$past(A)})
  );

  // data_out holds during reset (not written in reset branch)
  a_dataout_stable_in_reset: assert property (@(posedge clk)
    (!rst && !$isunknown($past(data_out))) |-> $stable(data_out)
  );

  // No X on data_out when past A/B were known and not in reset
  a_no_x_dataout: assert property (disable iff (!rst)
    !$isunknown($past({A,B})) |-> !$isunknown(data_out)
  );

  // Functional coverage
  c_enc:        cover property (disable iff (!rst) encrypt);
  c_dec:        cover property (disable iff (!rst) !encrypt);
  c_enc_dec_enc: cover property (disable iff (!rst) encrypt ##1 !encrypt ##1 encrypt);
  c_reset_cycle: cover property (@(negedge rst) ##1 rst);

endmodule

// Bind into DUT (accesses internal A/B/temp)
bind simple_encryption simple_encryption_sva u_simple_encryption_sva (
  .clk(clk),
  .rst(rst),
  .data_in(data_in),
  .key(key),
  .encrypt(encrypt),
  .data_out(data_out),
  .A(A),
  .B(B),
  .temp(temp)
);