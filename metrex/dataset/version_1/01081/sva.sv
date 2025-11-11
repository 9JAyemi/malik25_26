// SVA checker for ram16k_dualport
module ram16k_dualport_sva
  #(parameter int ADDR_W = 10,
    parameter int DATA_W = 32,
    parameter int DEPTH  = 4096)
(
    input logic                  CLK,
    input logic                  A1EN, B1EN,
    input logic [ADDR_W-1:0]     A1ADDR, B1ADDR,
    input logic [DATA_W-1:0]     B1DATA,
    input logic [DATA_W-1:0]     A1DATA
);

  default clocking cb @(posedge CLK); endclocking

  // Simple golden model (matches DUT ordering: read sees pre-write contents)
  logic [DATA_W-1:0] mem_ref [0:DEPTH-1];
  always_ff @(posedge CLK) begin
    if (B1EN && !$isunknown(B1ADDR) && !$isunknown(B1DATA))
      mem_ref[B1ADDR] <= B1DATA;
  end

  // Basic sanity on controls/inputs
  a_ctrl_known:          assert property ( !$isunknown(A1EN) && !$isunknown(B1EN) );
  a_read_inputs_known:   assert property ( A1EN |-> !$isunknown(A1ADDR) );
  a_write_inputs_known:  assert property ( B1EN |-> !$isunknown(B1ADDR) && !$isunknown(B1DATA) );

  // Synchronous read: on enable, A1DATA equals previous-state memory at A1ADDR
  a_read_data: assert property (
    A1EN && !$isunknown(A1ADDR) && !$isunknown(mem_ref[A1ADDR]) |-> A1DATA == mem_ref[A1ADDR]
  );

  // A1DATA updates only when A1EN is asserted
  a_change_only_on_en: assert property ( $changed(A1DATA) |-> $past(A1EN) );
  a_hold_when_disabled: assert property ( !A1EN |-> $stable(A1DATA) );

  // 1-cycle read-after-write returns newly written data
  a_raw_1cycle: assert property (
    B1EN && !$isunknown(B1ADDR) && !$isunknown(B1DATA)
    ##1 (A1EN && (A1ADDR == $past(B1ADDR)))
    |-> A1DATA == $past(B1DATA)
  );

  // No X on read when location is known-initialized in model
  a_no_x_on_read_initialized: assert property (
    A1EN && !$isunknown(mem_ref[A1ADDR]) |-> !$isunknown(A1DATA)
  );

  // Coverage
  c_write:                   cover property ( B1EN );
  c_read:                    cover property ( A1EN );
  c_same_cycle_collision:    cover property ( A1EN && B1EN && (A1ADDR == B1ADDR) );
  c_raw_1cycle:              cover property ( B1EN ##1 (A1EN && (A1ADDR == $past(B1ADDR))) );
  c_back_to_back_wr_same:    cover property ( B1EN ##1 (B1EN && (B1ADDR == $past(B1ADDR))) );

endmodule

// Bind example (instantiate per DUT instance)
// bind ram16k_dualport ram16k_dualport_sva #(.ADDR_W(10), .DATA_W(32), .DEPTH(4096))
//   sva ( .CLK(CLK), .A1EN(A1EN), .B1EN(B1EN), .A1ADDR(A1ADDR), .B1ADDR(B1ADDR), .B1DATA(B1DATA), .A1DATA(A1DATA) );