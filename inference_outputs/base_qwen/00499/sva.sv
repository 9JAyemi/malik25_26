module shift_register_sva (
    input logic clk,
    input logic reset,
    input logic parallel_load,
    input logic shift_left,
    input logic shift_right,
    input logic [3:0] parallel_input,
    output logic [3:0] q
);
    reg [3:0] register;

    always @(posedge clk) begin
        if (reset) begin
            register <= 4'b0000;
        end
        else begin
            if (parallel_load) begin
                register <= parallel_input;
            end
            else if (shift_left) begin
                register <= {register[2:0], 1'b0};
            end
            else if (shift_right) begin
                register <= {1'b0, register[3:1]};
            end
        end
    end

    assign q = register;

    ///// Register reset /////
    // At reset assertion, the register must be driven to 0.
    reset_register: assert property (
        @(posedge clk) disable iff (!reset) register == 4'b0000
    );

    ///// Parallel load /////
    // When parallel_load is asserted, the register must be loaded with parallel_input.
    parallel_load_check: assert property (
        @(posedge clk) disable iff (!reset) (parallel_load |-> register == parallel_input)
    );

    ///// Shift left /////
    // When shift_left is asserted, the register must shift left by one position.
    shift_left_check: assert property (
        @(posedge clk) disable iff (!reset) (shift_left |-> register == {register[2:0], 1'b0})
    );

    ///// Shift right /////
    // When shift_right is asserted, the register must shift right by one position.
    shift_right_check: assert property (
        @(posedge clk) disable iff (!reset) (shift_right |-> register == {1'b0, register[3:1]})
    );

    ///// Exclusive control /////
    // Only one of parallel_load, shift_left, or shift_right can be asserted at a time.
    exclusive_control: assert property (
        @(posedge clk) disable iff (!reset) !(parallel_load && shift_left) && !(parallel_load && shift_right) && !(shift_left && shift_right)
    );

endmodule