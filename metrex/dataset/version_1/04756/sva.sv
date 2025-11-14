// SVA checker for blockmem2rptr1w
// Focused, high-quality assertions with minimal scaffolding

module blockmem2rptr1w_sva
(
  input  logic         clk,
  input  logic         reset_n,

  input  logic  [7:0]  read_addr0,
  input  logic  [31:0] read_data0,
  input  logic  [31:0] read_data1,

  input  logic         rst,
  input  logic         cs,
  input  logic         wr,
  input  logic  [7:0]  write_addr,
  input  logic  [31:0] write_data,

  // internal DUT signals (bound hierarchically)
  input  logic  [31:0] tmp_read_data0,
  input  logic  [31:0] tmp_read_data1,
  input  logic  [7:0]  ptr_reg,
  input  logic  [7:0]  ptr_new,
  input  logic         ptr_we,
  input  var    logic  [31:0] mem [0:255]
);

  default clocking cb @(posedge clk); endclocking

  // past-valid guard for $past use
  logic past_valid;
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) past_valid <= 1'b0;
    else          past_valid <= 1'b1;
  end

  // track which memory locations have been initialized by a write
  logic [255:0] init_mask;
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) init_mask <= '0;
    else if (wr)  init_mask[write_addr] <= 1'b1;
  end

  // Wiring checks
  assert property (cb) (read_data0 === tmp_read_data0);
  assert property (cb) (read_data1 === tmp_read_data1);

  // Read semantics: synchronous read returns pre-write contents (old data)
  assert property (cb) past_valid |-> (tmp_read_data0 == $past(mem[read_addr0]));
  assert property (cb) past_valid |-> (tmp_read_data1 == $past(mem[ptr_reg]));

  // No X on reads when location has been written at least once
  assert property (cb) init_mask[read_addr0] |-> !$isunknown(tmp_read_data0));
  assert property (cb) init_mask[ptr_reg]    |-> !$isunknown(tmp_read_data1));

  // Write semantics: memory updates with write_data (visible next cycle)
  assert property (cb) wr |-> ##1 (mem[$past(write_addr)] == $past(write_data));

  // ptr_logic combinational intent sampled at clk
  assert property (cb) (ptr_we == (rst || cs));
  assert property (cb) cs  |-> (ptr_new == (ptr_reg + 8'h01));
  assert property (cb) rst && !cs |-> (ptr_new == 8'h00);
  assert property (cb) cs && (ptr_reg == 8'hFF) |-> (ptr_new == 8'h00); // wrap

  // ptr_reg update behavior (async reset_n, sync update on ptr_we)
  // Async reset drives ptr_reg to 0
  assert property (@(negedge reset_n) 1'b1 |-> (ptr_reg == 8'h00));
  // Hold when !ptr_we, load ptr_new when ptr_we
  assert property (cb) past_valid && reset_n && !ptr_we |-> (ptr_reg == $past(ptr_reg)));
  assert property (cb) past_valid && reset_n &&  ptr_we |-> (ptr_reg == $past(ptr_new)));

  // Same-cycle read-vs-write corner cases (explicit covers)
  cover property (cb) wr && (write_addr == read_addr0);  // RAW to read port 0 (old data)
  cover property (cb) wr && (write_addr == ptr_reg);     // RAW to read port 1 (old data)

  // Pointer control covers
  cover property (cb) rst && !cs;            // ptr load to 0
  cover property (cb) cs && !rst;            // ptr increment
  cover property (cb) rst && cs;             // both asserted: increment wins
  cover property (cb) cs && (ptr_reg==8'hFF); // wrap to 0
  cover property (@(negedge reset_n) 1'b1);  // async reset event

endmodule

// Bind the checker to the DUT
bind blockmem2rptr1w blockmem2rptr1w_sva i_blockmem2rptr1w_sva
(
  .clk,
  .reset_n,
  .read_addr0,
  .read_data0,
  .read_data1,
  .rst,
  .cs,
  .wr,
  .write_addr,
  .write_data,
  .tmp_read_data0(tmp_read_data0),
  .tmp_read_data1(tmp_read_data1),
  .ptr_reg(ptr_reg),
  .ptr_new(ptr_new),
  .ptr_we(ptr_we),
  .mem(mem)
);