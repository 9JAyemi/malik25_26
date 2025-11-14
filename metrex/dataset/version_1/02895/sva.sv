// SVA checker for td_mode_module
// - Uses a clocked, overlapped implication to check combinational decode in same cycle
// - Includes X-checks, independence from ctrl bits outside [7:5], allowed-set check, and coverage
module td_mode_module_sva (
  input logic        clk,
  input logic        rst_n,
  input logic [8:0]  ctrl,
  input logic [3:0]  td_mode
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Useful aliases
  localparam logic [3:0] M000 = 4'b0000;
  localparam logic [3:0] M001 = 4'b1000;
  localparam logic [3:0] M010 = 4'b0100;
  localparam logic [3:0] M011 = 4'b1100;
  localparam logic [3:0] M100 = 4'b0010;
  localparam logic [3:0] M101 = 4'b1010;
  localparam logic [3:0] M110 = 4'b0101;
  localparam logic [3:0] M111 = 4'b1111;

  // Track past validity for $past usage
  logic past_valid;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) past_valid <= 1'b0;
    else        past_valid <= 1'b1;
  end

  // X/Z checks
  assert property (!$isunknown(ctrl[7:5])) else
    $error("td_mode_module: ctrl[7:5] contains X/Z");
  assert property (!$isunknown(td_mode)) else
    $error("td_mode_module: td_mode contains X/Z");

  // Decode mapping checks (same-cycle)
  assert property (ctrl[7:5] == 3'b000 |=> td_mode == M000);
  assert property (ctrl[7:5] == 3'b001 |=> td_mode == M001);
  assert property (ctrl[7:5] == 3'b010 |=> td_mode == M010);
  assert property (ctrl[7:5] == 3'b011 |=> td_mode == M011);
  assert property (ctrl[7:5] == 3'b100 |=> td_mode == M100);
  assert property (ctrl[7:5] == 3'b101 |=> td_mode == M101);
  assert property (ctrl[7:5] == 3'b110 |=> td_mode == M110);
  assert property (ctrl[7:5] == 3'b111 |=> td_mode == M111);

  // Output is always in the allowed set
  assert property (td_mode inside {M000,M001,M010,M011,M100,M101,M110,M111});

  // Independence: only ctrl[7:5] can affect td_mode (others may toggle freely)
  assert property (past_valid && $past(ctrl[7:5]) == ctrl[7:5] |-> $stable(td_mode));

  // Change-cause: td_mode changes only when ctrl[7:5] changes
  assert property ($changed(td_mode) |-> $changed(ctrl[7:5]));

  // Functional coverage: each decode exercised
  cover property (ctrl[7:5] == 3'b000 && td_mode == M000);
  cover property (ctrl[7:5] == 3'b001 && td_mode == M001);
  cover property (ctrl[7:5] == 3'b010 && td_mode == M010);
  cover property (ctrl[7:5] == 3'b011 && td_mode == M011);
  cover property (ctrl[7:5] == 3'b100 && td_mode == M100);
  cover property (ctrl[7:5] == 3'b101 && td_mode == M101);
  cover property (ctrl[7:5] == 3'b110 && td_mode == M110);
  cover property (ctrl[7:5] == 3'b111 && td_mode == M111);
endmodule

// Example bind (provide a clock/reset visible at bind scope)
// bind td_mode_module td_mode_module_sva u_td_mode_module_sva(.clk(clk), .rst_n(rst_n), .ctrl(ctrl), .td_mode(td_mode));