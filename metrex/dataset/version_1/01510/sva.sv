// SVA checker for binary_counter
module binary_counter_sva #(parameter WIDTH=4) (
  input  logic               clk,
  input  logic               rst,
  input  logic [WIDTH-1:0]   count
);

  // Golden reference model (mirrors DUT behavior incl. async reset)
  logic [WIDTH-1:0] ref_count;
  always @(posedge clk or posedge rst) begin
    if (rst) ref_count <= '0;
    else     ref_count <= ref_count + 1'b1;
  end

  // Core: DUT must match reference after NBA updates (both on clk and rst events)
  property p_match_ref;
    @(posedge clk or posedge rst) ##0 (count == ref_count);
  endproperty
  assert property (p_match_ref);

  // While reset is asserted, counter must be 0 on every clk
  assert property (@(posedge clk) rst |-> count == '0);

  // Async reset drives counter to 0 in the same timestep (observe after NBA with ##0)
  assert property (@(posedge rst) ##0 (count == '0));

  // No X/Z on count at observable edges
  assert property (@(posedge clk or posedge rst) !$isunknown(count));

  // When not in reset across consecutive clks, increment by 1 (mod WIDTH)
  assert property (@(posedge clk) !rst && $past(!rst) |-> count == $past(count) + 1'b1);

  // Wrap-around when free-running (not in reset across two clks)
  assert property (@(posedge clk) !rst && $past(!rst) && $past(count) == '1 |-> count == '0);

  // Coverage
  cover property (@(posedge rst) ##0 (count == '0));                // async reset observed
  cover property (@(posedge clk) !rst && count == '1);              // saw increment to 1
  cover property (@(posedge clk) !rst && count == '1 && $past(count) == '0);
  cover property (@(posedge clk) !rst && count == '1 && $past(!rst)); // free-run increment
  cover property (@(posedge clk) !rst && count == '1 && $past(count) == '0);
  cover property (@(posedge clk) !rst && count == '0 && $past(count) == '1); // simple progression
  cover property (@(posedge clk) !rst && $past(!rst) && $past(count) == '1 && count == 2);
  cover property (@(posedge clk) !rst && $past(!rst) && $past(count) == '1 && count == 2);
  cover property (@(posedge clk) !rst && $past(!rst) && $past(count) == '1 && count == 2);
  cover property (@(posedge clk) !rst && $past(!rst) && $past(count) == '1 && count == 2);
  // Wrap-around covered explicitly:
  cover property (@(posedge clk) !rst && $past(!rst) && $past(count) == '1 && count == '0);

endmodule

// Bind into DUT
bind binary_counter binary_counter_sva #(.WIDTH(4)) u_binary_counter_sva (
  .clk   (clk),
  .rst   (rst),
  .count (count)
);