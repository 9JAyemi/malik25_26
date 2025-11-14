// SVA for light_control – concise, high-quality checks and coverage
// Bind-ready checker; no DUT/testbench changes needed.

module light_control_sva (
  input  logic [11:0] als,
  input  logic [11:0] dll,
  input  logic        en,
  input  logic [7:0]  dim
);
  default disable iff ($isunknown({als,dll,en}));

  // Expected behavior as a pure function (uses full precision before truncation)
  function automatic logic [7:0] exp_dim (logic [11:0] als_f, dll_f; logic en_f);
    logic [11:0] diff  = (als_f > dll_f) ? (als_f - dll_f) : 12'd0;
    logic [11:0] q12   = diff >> 4;
    return en_f ? ((q12 > 12'd255) ? 8'hFF : q12[7:0]) : 8'h00;
  endfunction

  // Core functional equivalence
  assert property (1'b1 |-> dim == exp_dim(als, dll, en));

  // Corner/intent clarity
  assert property (!en |-> dim == 8'h00);
  assert property (en && (als <= dll) |-> dim == 8'h00);
  assert property (en && (als > dll)  |-> dim == ((als - dll) >> 4));

  // No overflow possible on shift result when als > dll
  assert property (en && (als > dll) |-> (((als - dll) >> 4) <= 12'd255));

  // Output must be known when inputs are known
  assert property (!$isunknown(dim));

  // Boundary equivalences for 0xFF
  assert property (en && (als > dll) && ((als - dll) >= 12'd4080) |-> dim == 8'hFF);
  assert property (en && (dim == 8'hFF) |-> (als > dll) && ((als - dll) >= 12'd4080));

  // Functional coverage
  cover property (!en && dim == 8'h00);
  cover property (en && (als == dll) && dim == 8'h00);
  cover property (en && (als > dll) && ((als - dll) inside {[12'd1:12'd15]}) && dim == 8'h00);
  cover property (en && (als > dll) && ((als - dll) == 12'd16)  && dim == 8'd1);
  cover property (en && (als > dll) && ((als - dll) == 12'd4080) && dim == 8'hFF);
endmodule

bind light_control light_control_sva sva_i (.als(als), .dll(dll), .en(en), .dim(dim));