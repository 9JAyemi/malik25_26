module top_module_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [1:0] shift_amount,
    input logic shift_dir,
    input logic enable,
    input logic [1:0] select,
    input logic [15:0] out
);

// No RTL clock or reset; sample on clk. Assertions are combinational and disable iff enable==0.

    // When enable is LOW, out must be zero.
    check_enable_low_forces_zero: assert property (
        @(posedge clk) disable iff (enable == 1'b0) (out == 16'h0000)
    );

// When enable is HIGH, out must be one-hot.
    check_enable_high_onehot: assert property (
        @(posedge clk) disable iff (enable == 1'b0) $onehot(out)
    );

// When enable is HIGH and select==00, out must be 0001.
    check_select_00_maps_to_0001: assert property (
        @(posedge clk) disable iff (enable == 1'b0) (enable && (select == 2'b00)) |-> (out == 16'h0001)
    );

// When enable is HIGH and select==01, out must be 0010.
    check_select_01_maps_to_0010: assert property (
        @(posedge clk) disable iff (enable == 1'b0) (enable && (select == 2'b01)) |-> (out == 16'h0010)
    );

// When enable is HIGH and select==10, out must be 0100.
    check_select_10_maps_to_0100: assert property (
        @(posedge clk) disable iff (enable == 1'b0) (enable && (select == 2'b10)) |-> (out == 16'h0100)
    );

// When enable is HIGH and select==11, out must be 1000.
    check_select_11_maps_to_1000: assert property (
        @(posedge clk) disable iff (enable == 1'b0) (enable && (select == 2'b11)) |-> (out == 16'h1000)
    );

// When enable is HIGH and select==00, out[3:0] must be 0001.
    check_select_00_lsb: assert property (
        @(posedge clk) disable iff (enable == 1'b0) (enable && (select == 2'b00)) |-> (out[3:0] == 4'h1)
    );

// When enable is HIGH and select==01, out[3:0] must be 0010.
    check_select_01_lsb: assert property (
        @(posedge clk) disable iff (enable == 1'b0) (enable && (select == 2'b01)) |-> (out[3:0] == 4'h2)
    );

// When enable is HIGH and select==10, out[3:0] must be 0100.
    check_select_10_lsb: assert property (
        @(posedge clk) disable iff (enable == 1'b0) (enable && (select == 2'b10)) |-> (out[3:0] == 4'h4)
    );

// When enable is HIGH and select==11, out[3:0] must be 1000.
    check_select_11_lsb: assert property (
        @(posedge clk) disable iff (enable == 1'b0) (enable && (select == 2'b11)) |-> (out[3:0] == 4'h8)
    );

endmodule
