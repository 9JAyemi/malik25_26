module memory_sva #(
  parameter bits = 32,
  parameter words = 1024
)(
  input logic clk,
  input logic [9:0] addr,
  input logic [bits-1:0] data_in,
  input logic [bits-1:0] mem
);
    // Clock: clk (posedge). No reset in RTL.
    // Sequential: mem captures data_in when (addr < words), else holds.

    // If in-range last cycle, mem now equals last cycle's data_in.
    update_on_prev_in_range: assert property (
        @(posedge clk) disable iff ($initstate) $past(addr < words) |-> (mem == $past(data_in))
    );

    // If out-of-range last cycle, mem holds its previous value.
    hold_on_prev_out_of_range: assert property (
        @(posedge clk) disable iff ($initstate) !$past(addr < words) |-> (mem == $past(mem))
    );

    // Any change in mem requires in-range condition last cycle.
    change_requires_prev_in_range: assert property (
        @(posedge clk) disable iff ($initstate) (mem != $past(mem)) |-> $past(addr < words)
    );

    // When mem changes, the new value must equal last cycle's data_in.
    change_value_matches_prev_data_in: assert property (
        @(posedge clk) disable iff ($initstate) (mem != $past(mem)) |-> (mem == $past(data_in))
    );

    // Exact next-state function for mem based on previous cycle.
    next_state_function: assert property (
        @(posedge clk) disable iff ($initstate) mem == ($past(addr < words) ? $past(data_in) : $past(mem))
    );

    // If in-range last cycle and data_in differed from prior mem, mem must change.
    must_change_when_prev_in_range_and_data_differs: assert property (
        @(posedge clk) disable iff ($initstate) ($past(addr < words) && ($past(data_in) != $past(mem))) |-> (mem != $past(mem))
    );

    // If in-range last cycle and data_in equaled prior mem, mem must not change.
    no_change_when_prev_in_range_and_data_same: assert property (
        @(posedge clk) disable iff ($initstate) ($past(addr < words) && ($past(data_in) == $past(mem))) |-> (mem == $past(mem))
    );

    // If mem did not change, either last cycle was out-of-range or same data was captured.
    no_change_reason: assert property (
        @(posedge clk) disable iff ($initstate) (mem == $past(mem)) |-> (!$past(addr < words) || ($past(data_in) == $past(mem)))
    );

endmodule