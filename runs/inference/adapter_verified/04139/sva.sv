module ZigbeeReceiver_sva (
    input logic carrier,
    input logic modulated,
    input logic en,
    input logic clk,
    input logic [7:0] out
);

// When enabled and carrier is high, next cycle out equals {8{modulated}}.
    update_on_enable: assert property (
        @(posedge clk) (en && carrier) |=> (out == {8{modulated}})
    );

// When not enabled, next cycle out is zero.
    clear_when_disabled: assert property (
        @(posedge clk) !en |=> (out == 8'h00)
    );

// When enabled and carrier is low, next cycle out is zero.
    clear_when_carrier_low: assert property (
        @(posedge clk) (en && !carrier) |=> (out == 8'h00)
    );

// When enabled and carrier is high, next cycle MSB equals modulated.
    msb_matches_modulated: assert property (
        @(posedge clk) (en && carrier) |=> (out[7] == modulated)
    );

// When enabled and carrier is high, next cycle LSB equals modulated.
    lsb_matches_modulated: assert property (
        @(posedge clk) (en && carrier) |=> (out[0] == modulated)
    );

endmodule
