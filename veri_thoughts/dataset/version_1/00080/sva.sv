module shift_nor_sva (
    input logic        clk,
    input logic        load,
    input logic [1:0]  ena,
    input logic [99:0] data,
    input logic        a,
    input logic        b,
    input logic        out,
    input logic [99:0] shift_reg,
    input logic [99:0] shifted_data
);

    // Load captures data into the shift register on the next clock.
    check_load_captures_data: assert property (
        @(posedge clk) load |=> (shift_reg == $past(data))
    );

    // ena=01 rotates the shift register right by one bit when load is low.
    check_rotate_right: assert property (
        @(posedge clk) (!load && (ena == 2'b01)) |=> (shift_reg == {$past(shift_reg[0]), $past(shift_reg[99:1])})
    );

    // ena=10 rotates the shift register left by one bit when load is low.
    check_rotate_left: assert property (
        @(posedge clk) (!load && (ena == 2'b10)) |=> (shift_reg == {$past(shift_reg[98:0]), $past(shift_reg[99])})
    );

    // ena=00 or ena=11 holds the shift register value when load is low.
    check_hold_when_not_enabled: assert property (
        @(posedge clk) (!load && ((ena == 2'b00) || (ena == 2'b11))) |=> (shift_reg == $past(shift_reg))
    );

    // shifted_data always mirrors the shift register.
    check_shifted_data_mirrors_shift_reg: assert property (
        @(posedge clk) shifted_data == shift_reg
    );

    // out is always the NOR of inputs a and b.
    check_nor_output: assert property (
        @(posedge clk) out == ~(a | b)
    );

endmodule