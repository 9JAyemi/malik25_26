// SVA checker for Inverse_Clarke_Transform
// Bind this checker to the DUT. Provide a clock/reset in the TB.
// Focused on functional equivalence, sign-extension, truncation and saturation.

module ict_sva #(
  parameter int MULT = 56756
)(
  input logic clk,
  input logic rst_n,

  // DUT ports
  input  logic signed [17:0] alpha_voltage,
  input  logic signed [17:0] beta_voltage,
  input  logic signed [17:0] phase_voltages_0,
  input  logic signed [17:0] phase_voltages_1,
  input  logic signed [17:0] phase_voltages_2,

  // DUT internals
  input  logic signed [35:0] voltage_phase_a,
  input  logic signed [35:0] Gain1_out1,
  input  logic signed [35:0] Gain_out1,
  input  logic signed [35:0] voltage_phase_b,
  input  logic signed [37:0] Add1_cast,
  input  logic signed [37:0] Add1_cast_1,
  input  logic signed [37:0] Add1_sub_cast,
  input  logic signed [37:0] Add1_sub_temp,
  input  logic signed [35:0] voltage_phase_c,
  input  logic signed [35:0] Mux_out1_0,
  input  logic signed [35:0] Mux_out1_1,
  input  logic signed [35:0] Mux_out1_2,
  input  logic signed [17:0] Current_Data_Type_out1_0,
  input  logic signed [17:0] Current_Data_Type_out1_1,
  input  logic signed [17:0] Current_Data_Type_out1_2
);

  default clocking cb @(posedge clk); endclocking

  localparam logic signed [17:0] MAX18 = 18'sb0_11111111111111111;
  localparam logic signed [17:0] MIN18 = 18'sb1_00000000000000000;

  function automatic logic signed [17:0] sat18(input logic signed [35:0] x);
    if ((x[35] == 1'b0) && (x[34:30] != 5'b00000)) return MAX18;
    else if ((x[35] == 1'b1) && (x[34:30] != 5'b11111)) return MIN18;
    else return $signed(x[30:13]);
  endfunction

  // Stage-by-stage functional checks
  assert property (disable iff (!rst_n)
    voltage_phase_a == $signed({{2{alpha_voltage[17]}}, alpha_voltage, 16'b0})
  );

  assert property (disable iff (!rst_n)
    Gain_out1 == $signed({{3{alpha_voltage[17]}}, alpha_voltage, 15'b0})
  );

  assert property (disable iff (!rst_n)
    Gain1_out1 == $signed(MULT) * $signed(beta_voltage)
  );

  assert property (disable iff (!rst_n)
    voltage_phase_b == (Gain1_out1 - Gain_out1)
  );

  // Sign-extension, negate, add/sub chain
  assert property (disable iff (!rst_n)
    Add1_cast == $signed({{2{Gain_out1[35]}}, Gain_out1})
  );

  assert property (disable iff (!rst_n)
    Add1_sub_cast == $signed({{2{Gain1_out1[35]}}, Gain1_out1})
  );

  assert property (disable iff (!rst_n)
    Add1_cast_1 == -Add1_cast
  );

  assert property (disable iff (!rst_n)
    Add1_sub_temp == (Add1_cast_1 - Add1_sub_cast)
  );

  assert property (disable iff (!rst_n)
    voltage_phase_c == Add1_sub_temp[35:0]
  );

  // Mux mapping
  assert property (disable iff (!rst_n) Mux_out1_0 == voltage_phase_a);
  assert property (disable iff (!rst_n) Mux_out1_1 == voltage_phase_b);
  assert property (disable iff (!rst_n) Mux_out1_2 == voltage_phase_c);

  // Saturation/truncation and outputs
  assert property (disable iff (!rst_n)
    Current_Data_Type_out1_0 == sat18(Mux_out1_0)
  );
  assert property (disable iff (!rst_n)
    Current_Data_Type_out1_1 == sat18(Mux_out1_1)
  );
  assert property (disable iff (!rst_n)
    Current_Data_Type_out1_2 == sat18(Mux_out1_2)
  );

  assert property (disable iff (!rst_n)
    phase_voltages_0 == Current_Data_Type_out1_0
  );
  assert property (disable iff (!rst_n)
    phase_voltages_1 == Current_Data_Type_out1_1
  );
  assert property (disable iff (!rst_n)
    phase_voltages_2 == Current_Data_Type_out1_2
  );

  // Explicit saturation branch checks (sufficient and necessary)
  // Positive sat
  assert property (disable iff (!rst_n)
    ((Mux_out1_0[35]==0) && (Mux_out1_0[34:30]!=5'b00000)) |-> (phase_voltages_0 == MAX18)
  );
  assert property (disable iff (!rst_n)
    ((Mux_out1_1[35]==0) && (Mux_out1_1[34:30]!=5'b00000)) |-> (phase_voltages_1 == MAX18)
  );
  assert property (disable iff (!rst_n)
    ((Mux_out1_2[35]==0) && (Mux_out1_2[34:30]!=5'b00000)) |-> (phase_voltages_2 == MAX18)
  );

  // Negative sat
  assert property (disable iff (!rst_n)
    ((Mux_out1_0[35]==1) && (Mux_out1_0[34:30]!=5'b11111)) |-> (phase_voltages_0 == MIN18)
  );
  assert property (disable iff (!rst_n)
    ((Mux_out1_1[35]==1) && (Mux_out1_1[34:30]!=5'b11111)) |-> (phase_voltages_1 == MIN18)
  );
  assert property (disable iff (!rst_n)
    ((Mux_out1_2[35]==1) && (Mux_out1_2[34:30]!=5'b11111)) |-> (phase_voltages_2 == MIN18)
  );

  // Non-sat path
  assert property (disable iff (!rst_n)
    ((Mux_out1_0[35]==0 && Mux_out1_0[34:30]==5'b00000) ||
     (Mux_out1_0[35]==1 && Mux_out1_0[34:30]==5'b11111)) |->
     (phase_voltages_0 == $signed(Mux_out1_0[30:13]))
  );
  assert property (disable iff (!rst_n)
    ((Mux_out1_1[35]==0 && Mux_out1_1[34:30]==5'b00000) ||
     (Mux_out1_1[35]==1 && Mux_out1_1[34:30]==5'b11111)) |->
     (phase_voltages_1 == $signed(Mux_out1_1[30:13]))
  );
  assert property (disable iff (!rst_n)
    ((Mux_out1_2[35]==0 && Mux_out1_2[34:30]==5'b00000) ||
     (Mux_out1_2[35]==1 && Mux_out1_2[34:30]==5'b11111)) |->
     (phase_voltages_2 == $signed(Mux_out1_2[30:13]))
  );

  // Minimal coverage: normal and both saturation modes for each output, plus zero case
  cover property (disable iff (!rst_n)
    (alpha_voltage==0 && beta_voltage==0) && (phase_voltages_0==0) && (phase_voltages_1==0) && (phase_voltages_2==0)
  );

  cover property (disable iff (!rst_n)
    (Mux_out1_0[35]==0 && Mux_out1_0[34:30]!=5'b00000) && (phase_voltages_0==MAX18)
  );
  cover property (disable iff (!rst_n)
    (Mux_out1_0[35]==1 && Mux_out1_0[34:30]!=5'b11111) && (phase_voltages_0==MIN18)
  );
  cover property (disable iff (!rst_n)
    ((Mux_out1_0[35]==0 && Mux_out1_0[34:30]==5'b00000) ||
     (Mux_out1_0[35]==1 && Mux_out1_0[34:30]==5'b11111)) && (phase_voltages_0==$signed(Mux_out1_0[30:13]))
  );

  cover property (disable iff (!rst_n)
    (Mux_out1_1[35]==0 && Mux_out1_1[34:30]!=5'b00000) && (phase_voltages_1==MAX18)
  );
  cover property (disable iff (!rst_n)
    (Mux_out1_1[35]==1 && Mux_out1_1[34:30]!=5'b11111) && (phase_voltages_1==MIN18)
  );
  cover property (disable iff (!rst_n)
    ((Mux_out1_1[35]==0 && Mux_out1_1[34:30]==5'b00000) ||
     (Mux_out1_1[35]==1 && Mux_out1_1[34:30]==5'b11111)) && (phase_voltages_1==$signed(Mux_out1_1[30:13]))
  );

  cover property (disable iff (!rst_n)
    (Mux_out1_2[35]==0 && Mux_out1_2[34:30]!=5'b00000) && (phase_voltages_2==MAX18)
  );
  cover property (disable iff (!rst_n)
    (Mux_out1_2[35]==1 && Mux_out1_2[34:30]!=5'b11111) && (phase_voltages_2==MIN18)
  );
  cover property (disable iff (!rst_n)
    ((Mux_out1_2[35]==0 && Mux_out1_2[34:30]==5'b00000) ||
     (Mux_out1_2[35]==1 && Mux_out1_2[34:30]==5'b11111)) && (phase_voltages_2==$signed(Mux_out1_2[30:13]))
  );

endmodule

// Example bind (instantiate once per DUT). Drive clk/rst_n from TB.
bind Inverse_Clarke_Transform ict_sva #(.MULT(56756)) ict_sva_i (
  .clk(clk),
  .rst_n(rst_n),
  .alpha_voltage(alpha_voltage),
  .beta_voltage(beta_voltage),
  .phase_voltages_0(phase_voltages_0),
  .phase_voltages_1(phase_voltages_1),
  .phase_voltages_2(phase_voltages_2),
  .voltage_phase_a(voltage_phase_a),
  .Gain1_out1(Gain1_out1),
  .Gain_out1(Gain_out1),
  .voltage_phase_b(voltage_phase_b),
  .Add1_cast(Add1_cast),
  .Add1_cast_1(Add1_cast_1),
  .Add1_sub_cast(Add1_sub_cast),
  .Add1_sub_temp(Add1_sub_temp),
  .voltage_phase_c(voltage_phase_c),
  .Mux_out1_0(Mux_out1[0]),
  .Mux_out1_1(Mux_out1[1]),
  .Mux_out1_2(Mux_out1[2]),
  .Current_Data_Type_out1_0(Current_Data_Type_out1[0]),
  .Current_Data_Type_out1_1(Current_Data_Type_out1[1]),
  .Current_Data_Type_out1_2(Current_Data_Type_out1[2])
);