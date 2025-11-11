// SVA for binary_search
// Bindable assertions focusing on correctness, corner cases, and concise coverage

module binary_search_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [31:0] target,
  input  logic [31:0] data,
  input  logic        found,
  input  logic [4:0]  index,
  input  logic [4:0]  low,
  input  logic [4:0]  high,
  input  logic [4:0]  mid
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // past-valid helper
  logic past_valid;
  always @(posedge clk or posedge reset) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  // Asynchronous-reset observable at clock edge
  assert property (@(posedge clk) reset |-> (found==1'b0 && index==5'd31 && low==5'd0 && high==5'd31));

  // Bounds
  assert property (low  <= 5'd31);
  assert property (high <= 5'd31);
  assert property (index<= 5'd31);
  assert property (found |-> index<=5'd31);

  // mid update uses previous low/high; check correct math (with widened sum to avoid overflow)
  assert property (past_valid && $past(low) <= $past(high)
                   |-> mid == ((({1'b0,$past(low)} + {1'b0,$past(high)}) >> 1)[4:0])
                    && mid >= $past(low) && mid <= $past(high)));

  // Detect overflow risk in mid computation (design bug if this ever triggers)
  assert property (past_valid && $past(low) <= $past(high)
                   |-> ({1'b0,$past(low)} + {1'b0,$past(high)}) < 6'd32);

  // Branch behavior (uses previous mid)
  assert property (past_valid && $past(low) <= $past(high) && (data[$past(mid)] == target)
                   |=> found && index==$past(mid) && low==$past(low) && high==$past(high));

  assert property (past_valid && $past(low) <= $past(high) && (data[$past(mid)] > target)
                   |=> high==$past(mid)-5'd1 && low==$past(low) && found==$past(found) && index==$past(index));

  assert property (past_valid && $past(low) <= $past(high) && (data[$past(mid)] < target)
                   |=> low==$past(mid)+5'd1 && high==$past(high) && found==$past(found) && index==$past(index));

  // Termination (not found)
  assert property (past_valid && $past(low) > $past(high)
                   |=> found==1'b0 && index==5'd31 && low==$past(low) && high==$past(high));

  // Monotonic narrowing when not equal
  assert property (past_valid && $past(low) <= $past(high) && !(data[$past(mid)] == target)
                   |=> low >= $past(low) && high <= $past(high) && (low != $past(low) ^ high != $past(high)));

  // Stickiness after found
  assert property (found |=> found && index==$past(index));

  // Width-mismatch sanity: with current DUT, data[mid] is 1-bit; equality only possible for target==0/1
  assert property (found |-> (target==32'd0 || target==32'd1));
  assert property (found && target==32'd1 |-> data[$past(index)]==1'b1);
  assert property (found && target==32'd0 |-> data[$past(index)]==1'b0);

  // Underflow/overflow hazards on bound updates (would indicate wrong arithmetic width)
  assert property (!(past_valid && $past(low) <= $past(high) && (data[$past(mid)] > target) && $past(mid)==5'd0));
  assert property (!(past_valid && $past(low) <= $past(high) && (data[$past(mid)] < target) && $past(mid)==5'd31));

  // Coverage
  cover property (past_valid && found);
  cover property (past_valid && $past(low) <= $past(high) && (data[$past(mid)] > target));
  cover property (past_valid && $past(low) <= $past(high) && (data[$past(mid)] < target));
  cover property (past_valid && found && index==5'd0);
  cover property (past_valid && found && index==5'd31);
  cover property (past_valid && $past(low) > $past(high) && !found);

endmodule

// Bind to DUT (accessing internal low/high/mid)
bind binary_search binary_search_sva bsv (
  .clk(clk),
  .reset(reset),
  .target(target),
  .data(data),
  .found(found),
  .index(index),
  .low(low),
  .high(high),
  .mid(mid)
);