// SVA for shift_register_counter
module shift_register_counter_sva (
    input  logic        clk,
    input  logic        reset,
    input  logic [7:0]  d,
    input  logic        select,
    input  logic [7:0]  q,
    input  logic [7:0]  shift_reg,
    input  logic [3:0]  counter
);

    // Combinational output relation
    assert property (@(posedge clk) q == (shift_reg & {4'hF, counter}));

    // Reset behavior (synchronous)
    assert property (@(posedge clk) $past(reset) |-> (shift_reg == 8'h5A && counter == 4'h0));

    // Shift behavior when select=1 (and not coming right out of reset)
    assert property (@(posedge clk) disable iff (reset)
        (select && !$past(reset)) |-> (shift_reg == {$past(shift_reg[6:0]), $past(d[0])} && counter == $past(counter)));

    // Count behavior when select=0 (and not coming right out of reset)
    assert property (@(posedge clk) disable iff (reset)
        (!select && !$past(reset)) |-> (shift_reg == $past(shift_reg) &&
                                        ((counter == ($past(counter) + 4'd1)) ||
                                         ($past(counter) == 4'hF && counter == 4'h0))));

    // No unintended updates
    assert property (@(posedge clk) disable iff (reset)
        (select && !$past(reset)) |-> $stable(counter));
    assert property (@(posedge clk) disable iff (reset)
        (!select && !$past(reset)) |-> $stable(shift_reg));

    // Nibble-level mapping checks
    assert property (@(posedge clk) q[7:4] == shift_reg[7:4]);
    assert property (@(posedge clk) q[3:0] == (shift_reg[3:0] & counter));

    // Coverage
    cover property (@(posedge clk) reset);
    cover property (@(posedge clk) disable iff (reset) (select && !$past(reset) &&
                     shift_reg == {$past(shift_reg[6:0]), 1'b0}));
    cover property (@(posedge clk) disable iff (reset) (select && !$past(reset) &&
                     shift_reg == {$past(shift_reg[6:0]), 1'b1}));
    cover property (@(posedge clk) disable iff (reset) (!select && !$past(reset) &&
                     counter == ($past(counter) + 4'd1)));
    cover property (@(posedge clk) disable iff (reset) ($past(counter) == 4'hF && !select ##1 counter == 4'h0));
    cover property (@(posedge clk) disable iff (reset) (q[3:0] == 4'h0));           // counter=0 effect
    cover property (@(posedge clk) disable iff (reset) (q[3:0] == shift_reg[3:0])); // counter=4'hF effect
endmodule

// Bind into DUT
bind shift_register_counter shift_register_counter_sva sva_i (
    .clk(clk),
    .reset(reset),
    .d(d),
    .select(select),
    .q(q),
    .shift_reg(shift_reg),
    .counter(counter)
);