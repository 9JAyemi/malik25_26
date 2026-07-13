module adder_module_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [3:0] input_val,
    input logic [3:0] output_val
);
    // Reset drives output_val to zero whenever rst is HIGH.
    reset_forces_zero: assert property (
        @(posedge clk) rst |-> (output_val == 4'b0000)
    );

    // On enable with reset low, next-cycle output equals (previous input_val + 0xB) modulo 16.
    update_on_enable: assert property (
        @(posedge clk) disable iff (rst)
            (en && !rst) |=> (!rst && (output_val == (($past(input_val) + 4'b1011)[3:0])))
    );

    // With enable low and reset low, output holds its previous value next cycle.
    hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst)
            (!en && !rst) |=> (!rst && (output_val == $past(output_val)))
    );

    // Any change in output across cycles (with reset low both cycles) requires prior enable high.
    change_requires_enable: assert property (
        @(posedge clk) disable iff (rst)
            (!rst && !$past(rst) && (output_val != $past(output_val))) |-> $past(en)
    );

    // If reset rises between cycles, at this clock edge output is zero.
    reset_rise_clears_output: assert property (
        @(posedge clk) $rose(rst) |-> (output_val == 4'b0000)
    );

    // If reset is low in consecutive cycles and enable was low, output remains unchanged.
    stable_without_enable_two_cycles: assert property (
        @(posedge clk) disable iff (rst)
            (!rst && !$past(rst) && !$past(en)) |-> (output_val == $past(output_val))
    );
endmodule