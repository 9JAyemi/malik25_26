// SVA checker for RegFile_3port
// Bind this module to the DUT instance
module RegFile_3port_sva #(
  parameter data_width = 8,
  parameter addr_width = 4,
  parameter depth      = 1<<addr_width
)(
  input logic                      CLK,
  input logic                      rst_n,
  input logic [addr_width-1:0]     ADDR_IN1,
  input logic [data_width-1:0]     D_IN1,
  input logic                      WE1,
  input logic [addr_width-1:0]     ADDR_IN2,
  input logic [data_width-1:0]     D_IN2,
  input logic                      WE2,
  input logic [addr_width-1:0]     ADDR_OUT1,
  input logic [addr_width-1:0]     ADDR_OUT2,
  input logic [addr_width-1:0]     ADDR_OUT3,
  input logic [data_width-1:0]     D_OUT1,
  input logic [data_width-1:0]     D_OUT2,
  input logic [data_width-1:0]     D_OUT3
);

  // Simple reference model that mirrors DUT semantics (WE1 then WE2; WE2 wins on same addr)
  logic [data_width-1:0] ref_mem [0:depth-1];

  always_ff @(posedge CLK) begin
    if (!rst_n) begin
      foreach (ref_mem[i]) ref_mem[i] <= '0;
    end else begin
      if (WE1) ref_mem[ADDR_IN1] <= D_IN1;
      if (WE2) ref_mem[ADDR_IN2] <= D_IN2;
    end
  end

  // Reset: outputs must be 0 immediately after the clock (post-NBA)
  property p_reset_zero;
    @(posedge CLK) (!rst_n) |-> ##0 (D_OUT1=='0 && D_OUT2=='0 && D_OUT3=='0);
  endproperty
  assert property (p_reset_zero);

  // Functional correctness: all reads match the reference model (post-NBA)
  property p_read_matches_model;
    @(posedge CLK) rst_n |-> ##0 (
      (D_OUT1 == ref_mem[ADDR_OUT1]) &&
      (D_OUT2 == ref_mem[ADDR_OUT2]) &&
      (D_OUT3 == ref_mem[ADDR_OUT3])
    );
  endproperty
  assert property (p_read_matches_model);

  // Same-cycle read-after-write behavior per port (including priority on collisions)
  // Port 1 sees WE2 if its address matches IN2, else WE1 if matches IN1, else existing ref data
  property p_raw_port1;
    @(posedge CLK) rst_n |-> ##0 (
      (WE2 && (ADDR_OUT1==ADDR_IN2)) ? (D_OUT1==D_IN2) :
      (WE1 && (!WE2 || (ADDR_IN1!=ADDR_IN2)) && (ADDR_OUT1==ADDR_IN1)) ? (D_OUT1==D_IN1) :
      1'b1  // otherwise checked by p_read_matches_model
    );
  endproperty
  assert property (p_raw_port1);

  property p_raw_port2;
    @(posedge CLK) rst_n |-> ##0 (
      (WE2 && (ADDR_OUT2==ADDR_IN2)) ? (D_OUT2==D_IN2) :
      (WE1 && (!WE2 || (ADDR_IN1!=ADDR_IN2)) && (ADDR_OUT2==ADDR_IN1)) ? (D_OUT2==D_IN1) :
      1'b1
    );
  endproperty
  assert property (p_raw_port2);

  property p_raw_port3;
    @(posedge CLK) rst_n |-> ##0 (
      (WE2 && (ADDR_OUT3==ADDR_IN2)) ? (D_OUT3==D_IN2) :
      (WE1 && (!WE2 || (ADDR_IN1!=ADDR_IN2)) && (ADDR_OUT3==ADDR_IN1)) ? (D_OUT3==D_IN1) :
      1'b1
    );
  endproperty
  assert property (p_raw_port3);

  // Explicit collision priority check: if both write same addr, any same-cycle read must see D_IN2
  property p_collision_priority_port1;
    @(posedge CLK) rst_n && WE1 && WE2 && (ADDR_IN1==ADDR_IN2) && (ADDR_OUT1==ADDR_IN1)
      |-> ##0 (D_OUT1==D_IN2);
  endproperty
  assert property (p_collision_priority_port1);

  property p_collision_priority_port2;
    @(posedge CLK) rst_n && WE1 && WE2 && (ADDR_IN1==ADDR_IN2) && (ADDR_OUT2==ADDR_IN1)
      |-> ##0 (D_OUT2==D_IN2);
  endproperty
  assert property (p_collision_priority_port2);

  property p_collision_priority_port3;
    @(posedge CLK) rst_n && WE1 && WE2 && (ADDR_IN1==ADDR_IN2) && (ADDR_OUT3==ADDR_IN1)
      |-> ##0 (D_OUT3==D_IN2);
  endproperty
  assert property (p_collision_priority_port3);

  // X/Z hygiene (after reset released): no X on key inputs; outputs remain known post-NBA
  property p_no_x_inputs;
    @(posedge CLK) rst_n |-> !$isunknown({WE1,WE2,ADDR_IN1,ADDR_IN2,ADDR_OUT1,ADDR_OUT2,ADDR_OUT3,D_IN1,D_IN2});
  endproperty
  assert property (p_no_x_inputs);

  property p_no_x_outputs;
    @(posedge CLK) rst_n |-> ##0 !$isunknown({D_OUT1,D_OUT2,D_OUT3});
  endproperty
  assert property (p_no_x_outputs);

  // ----------------------------------
  // Functional coverage (concise, key scenarios)
  // ----------------------------------

  // Any write activity
  cover property (@(posedge CLK) rst_n && (WE1 || WE2));

  // Concurrent two-port writes to different addresses
  cover property (@(posedge CLK) rst_n && WE1 && WE2 && (ADDR_IN1!=ADDR_IN2));

  // Collision (both write same address)
  cover property (@(posedge CLK) rst_n && WE1 && WE2 && (ADDR_IN1==ADDR_IN2));

  // Same-cycle read-after-write per port for WE1 (no collision on that addr)
  cover property (@(posedge CLK) rst_n && WE1 && (!WE2 || (ADDR_IN1!=ADDR_IN2)) && (ADDR_OUT1==ADDR_IN1));
  cover property (@(posedge CLK) rst_n && WE1 && (!WE2 || (ADDR_IN1!=ADDR_IN2)) && (ADDR_OUT2==ADDR_IN1));
  cover property (@(posedge CLK) rst_n && WE1 && (!WE2 || (ADDR_IN1!=ADDR_IN2)) && (ADDR_OUT3==ADDR_IN1));

  // Same-cycle read-after-write per port for WE2 (covers priority case too)
  cover property (@(posedge CLK) rst_n && WE2 && (ADDR_OUT1==ADDR_IN2));
  cover property (@(posedge CLK) rst_n && WE2 && (ADDR_OUT2==ADDR_IN2));
  cover property (@(posedge CLK) rst_n && WE2 && (ADDR_OUT3==ADDR_IN2));

  // All three read ports reading the same address
  cover property (@(posedge CLK) rst_n && (ADDR_OUT1==ADDR_OUT2) && (ADDR_OUT2==ADDR_OUT3));

endmodule

// Example bind (place in a package or a top-level SV file):
// bind RegFile_3port RegFile_3port_sva #(.data_width(data_width), .addr_width(addr_width), .depth(depth)) u_regfile_3p_sva (
//   .CLK(CLK), .rst_n(rst_n),
//   .ADDR_IN1(ADDR_IN1), .D_IN1(D_IN1), .WE1(WE1),
//   .ADDR_IN2(ADDR_IN2), .D_IN2(D_IN2), .WE2(WE2),
//   .ADDR_OUT1(ADDR_OUT1), .ADDR_OUT2(ADDR_OUT2), .ADDR_OUT3(ADDR_OUT3),
//   .D_OUT1(D_OUT1), .D_OUT2(D_OUT2), .D_OUT3(D_OUT3)
// );