// SVA for pll_lock_lookup
// Concise checks + coverage; bind these to the DUT

// 1) Main SVA module (no dependency on unpacked array ports)
module pll_lock_lookup_sva #(parameter int unsigned VALID_MAX_ADDR = 60)
(
  input  logic        clk,
  input  logic [6:0]  divider,
  input  logic [5:0]  addr,
  input  logic [39:0] value
);
  localparam int unsigned DIV_MAX = VALID_MAX_ADDR + 1; // max legal divider

  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  a_no_x_divider: assert property (!$isunknown(divider));
  a_no_x_addr   : assert property (!$isunknown(addr));
  a_no_x_value  : assert property (!$isunknown(value));

  // Legal range (prevents 7->6 bit truncation and use of uninitialized table rows)
  a_divider_range: assert property (divider inside {[7'd1:7'(DIV_MAX)]});
  a_addr_range   : assert property (addr <= 6'(VALID_MAX_ADDR));

  // Address derivation matches spec (lower 6 bits of divider-1)
  a_addr_calc: assert property (addr == (divider - 7'd1)[5:0]);

  // Output must be functionally stable if input is stable
  a_hold: assert property ($stable(divider) |-> $stable(value));

  // Structural invariants of the 40-bit entry (from the table contents)
  a_dup_5b_fields: assert property (value[39:35] == value[34:30]);
  a_const_field4 : assert property (value[19:10] == 10'h3E9); // 1111101001
  a_const_field5 : assert property (value[9:0]   == 10'h001);

  // Coverage: hit every used address, edges, and representative data patterns
  genvar i;
  generate
    for (i = 0; i <= VALID_MAX_ADDR; i++) begin : cv_addr
      cover property (addr == i);
    end
  endgenerate
  cv_div_min : cover property (divider == 7'd1);
  cv_div_max : cover property (divider == 7'(DIV_MAX));
  cv_illegal0: cover property (divider == 7'd0);
  cv_illegalH: cover property (divider >  7'(DIV_MAX));

  // Representative 10-bit field[29:20] values seen in the table
  cv_f3_hi : cover property (value[29:20] == 10'h3E8); // 1111101000
  cv_f3_mid: cover property (value[29:20] == 10'h384); // 1110000100
  cv_f3_lo : cover property (value[29:20] == 10'h0FA); // 0011111010

  // Saturation of first 5-bit field
  cv_5b_lo : cover property (value[39:35] == 5'b00110);
  cv_5b_hi : cover property (value[39:35] == 5'b11111);
endmodule

// 2) Bind the SVA module
bind pll_lock_lookup pll_lock_lookup_sva
  #(.VALID_MAX_ADDR(60))
  u_pll_lock_lookup_sva (
    .clk(clk),
    .divider(divider),
    .addr(addr),
    .value(value)
  );

// 3) Direct bound check that output equals the table entry selected
//    (references DUT's internal array)
bind pll_lock_lookup a_value_matches_lookup:
  assert property (@(posedge clk) value == lookup[addr]);