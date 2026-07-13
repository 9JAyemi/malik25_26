module top_module_sva(
    input logic clk,
    input logic reset,
    input logic load,
    input logic ena,
    input logic [3:0] data_in,
    input logic [3:0] data_out,
    input logic [3:0] shift_reg,
    input logic [1:0] select,
    input logic [3:0] shifted_data
);

    // Synchronous reset clears the shift register.
    check_reset_clears_shift_reg: assert property (
        @(posedge clk) reset |=> (shift_reg == 4'b0000)
    );

    // Load takes priority and captures data_in.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (shift_reg == $past(data_in))
    );

    // Enable rotates the register when load is low.
    check_enable_rotates_shift_reg: assert property (
        @(posedge clk) disable iff (reset)
        (!load && ena) |=> (shift_reg == {$past(shift_reg[2:0]), $past(shift_reg[3])})
    );

    // The register holds its value when idle.
    check_idle_holds_shift_reg: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !ena) |=> (shift_reg == $past(shift_reg))
    );

    // select[0] matches its decoder equation.
    check_select0_decode: assert property (
        @(posedge clk) disable iff (reset)
        (select[0] == (~shift_reg[3] & ~shift_reg[2]))
    );

    // select[1] matches its decoder equation.
    check_select1_decode: assert property (
        @(posedge clk) disable iff (reset)
        (select[1] == (~shift_reg[3] & shift_reg[2]))
    );

    // shifted_data is formed from shift_reg[1:0] with two zeros.
    check_shifted_data_value: assert property (
        @(posedge clk) disable iff (reset)
        (shifted_data == {shift_reg[1:0], 2'b00})
    );

    // data_out follows data_in during load.
    check_data_out_on_load: assert property (
        @(posedge clk) disable iff (reset)
        load |-> (data_out == data_in)
    );

    // data_out selects shifted_data when select[1] is high.
    check_data_out_shifted_path: assert property (
        @(posedge clk) disable iff (reset)
        (!load && select[1]) |-> (data_out == shifted_data)
    );

    // data_out selects shift_reg when select[1] is low.
    check_data_out_register_path: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !select[1]) |-> (data_out == shift_reg)
    );

endmodule