module num_to_digits_sva (
    input  logic        clk,
    input  logic [11:0] _num,
    input  logic [3:0]  _thousands,
    input  logic [3:0]  _hundreds,
    input  logic [3:0]  _tens,
    input  logic [3:0]  _ones
);
    // Thousands equals (_num % 10000)/1000.
    check_thousands_calc: assert property (
        @(posedge clk) disable iff (1'b0)
        _thousands == ((_num % 14'd10000) / 10'd1000)
    );

    // Hundreds equals (_num % 1000)/100.
    check_hundreds_calc: assert property (
        @(posedge clk) disable iff (1'b0)
        _hundreds == ((_num % 10'd1000) / 7'd100)
    );

    // Tens equals (_num % 100)/10.
    check_tens_calc: assert property (
        @(posedge clk) disable iff (1'b0)
        _tens == ((_num % 7'd100) / 4'd10)
    );

    // Ones equals _num % 10.
    check_ones_calc: assert property (
        @(posedge clk) disable iff (1'b0)
        _ones == (_num % 4'd10)
    );

    // Thousands digit is in 0..9.
    check_thousands_range: assert property (
        @(posedge clk) disable iff (1'b0)
        _thousands <= 4'd9
    );

    // Hundreds digit is in 0..9.
    check_hundreds_range: assert property (
        @(posedge clk) disable iff (1'b0)
        _hundreds <= 4'd9
    );

    // Tens digit is in 0..9.
    check_tens_range: assert property (
        @(posedge clk) disable iff (1'b0)
        _tens <= 4'd9
    );

    // Ones digit is in 0..9.
    check_ones_range: assert property (
        @(posedge clk) disable iff (1'b0)
        _ones <= 4'd9
    );

    // Recomposition: 1000*T + 100*H + 10*D + O equals _num % 10000.
    check_decimal_recomposition: assert property (
        @(posedge clk) disable iff (1'b0)
        ((((_thousands * 4'd10) + _hundreds) * 4'd10 + _tens) * 4'd10 + _ones) == (_num % 14'd10000)
    );

    // For _num < 1000, thousands must be 0.
    check_thousands_zero_below_1000: assert property (
        @(posedge clk) disable iff (1'b0)
        (_num < 10'd1000) |-> (_thousands == 4'd0)
    );

    // For _num < 100, hundreds must be 0.
    check_hundreds_zero_below_100: assert property (
        @(posedge clk) disable iff (1'b0)
        (_num < 7'd100) |-> (_hundreds == 4'd0)
    );

    // For _num < 10, tens must be 0.
    check_tens_zero_below_10: assert property (
        @(posedge clk) disable iff (1'b0)
        (_num < 4'd10) |-> (_tens == 4'd0)
    );
endmodule