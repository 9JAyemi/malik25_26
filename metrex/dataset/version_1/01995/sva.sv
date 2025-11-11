// SVA checker for memory_controller
// Notes:
// - Uses an external sample clock/reset from the testbench (clk, rst_n).
// - Binds into the DUT and taps internal 'state'.
// - Concise but covers decode, transitions, mutual exclusion, data behavior, X checks, and key coverage.

module mc_sva #(
  parameter int n = 8,
  parameter int m = 32
)(
  input  logic                  clk,
  input  logic                  rst_n,

  // DUT ports
  input  logic [n-1:0]          addr,
  input  logic                  we,
  input  logic [m-1:0]          data,
  input  logic                  mem_we,
  input  logic                  mem_re,
  input  logic [m-1:0]          mem_data,

  // DUT internal
  input  logic [n-1:0]          state
);

  default clocking cb @(posedge clk); endclocking

  // Track last written data for data persistence checks
  logic        seen_wr;
  logic [m-1:0] last_wr;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      seen_wr <= 1'b0;
      last_wr <= '0;
    end else if (mem_we) begin
      seen_wr <= 1'b1;
      last_wr <= data;
    end
  end

  // Basic hygiene: no X/Z on key outputs and state in-active
  assert property (disable iff (!rst_n) !$isunknown({mem_we, mem_re, mem_data, state}));
  // State encoding limited to 0..3 and upper bits zero
  assert property (disable iff (!rst_n) state inside {[0:3]});
  if (n > 2) begin
    assert property (disable iff (!rst_n) state[n-1:2] == '0);
  end

  // Outputs mutually exclusive
  assert property (disable iff (!rst_n) !(mem_we && mem_re));

  // Output decode matches state
  assert property (disable iff (!rst_n) (state == 1) |-> (mem_we && !mem_re));
  assert property (disable iff (!rst_n) (state == 2) |-> (!mem_we && mem_re));
  assert property (disable iff (!rst_n) (state == 0 || state == 3) |-> (!mem_we && !mem_re));
  // Stronger: outputs imply state
  assert property (disable iff (!rst_n) mem_we |-> state == 1);
  assert property (disable iff (!rst_n) mem_re |-> state == 2);

  // Next-state transition function (sampled on clk)
  assert property (disable iff (!rst_n) (state == 0 && we)  |=> state == 1);
  assert property (disable iff (!rst_n) (state == 0 && !we) |=> state == 2);
  assert property (disable iff (!rst_n) (state == 1)        |=> state == 0);
  assert property (disable iff (!rst_n) (state == 2)        |=> state == 3);
  assert property (disable iff (!rst_n) (state == 3)        |=> state == 0);

  // Write behavior: when writing, mem_data must equal data
  assert property (disable iff (!rst_n) mem_we |-> mem_data == data);

  // Data persistence: after any write, mem_data should hold the last written value until next write
  assert property (disable iff (!rst_n || !$past(rst_n)) (!mem_we && seen_wr) |-> mem_data == $past(mem_data));
  assert property (disable iff (!rst_n) seen_wr |-> mem_data == last_wr);

  // Read behavior: reads must not assert write, and must not disturb data
  assert property (disable iff (!rst_n) mem_re |-> !mem_we);
  assert property (disable iff (!rst_n || !$past(rst_n)) mem_re |-> mem_data == $past(mem_data));

  // Bounded progress from idle back to idle (both paths)
  assert property (disable iff (!rst_n) (state == 0 && we)  |-> ##2 state == 0);
  assert property (disable iff (!rst_n) (state == 0 && !we) |-> ##3 state == 0);

  // Coverage
  cover property (disable iff (!rst_n) mem_we);
  cover property (disable iff (!rst_n) mem_re);
  cover property (disable iff (!rst_n) (state == 0 && we)  ##1 (state == 1) ##1 (state == 0));
  cover property (disable iff (!rst_n) (state == 0 && !we) ##1 (state == 2) ##1 (state == 3) ##1 (state == 0));
  cover property (disable iff (!rst_n) seen_wr && mem_we && (data != last_wr));

endmodule

// Bind into the DUT; provide clk/rst_n from your testbench
// Example:
// logic tb_clk, tb_rst_n;
// bind memory_controller mc_sva #(.n(n), .m(m)) u_mc_sva (
//   .clk(tb_clk), .rst_n(tb_rst_n),
//   .addr(addr), .we(we), .data(data),
//   .mem_we(mem_we), .mem_re(mem_re), .mem_data(mem_data),
//   .state(state)
// );