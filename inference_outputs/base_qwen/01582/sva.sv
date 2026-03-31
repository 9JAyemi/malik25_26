```systemverilog
module register_4bit_sva (
    input logic [3:0] data_in,
    input logic load,
    input logic reset,
    input logic clk,
    output logic [3:0] Q
);
    // Local signals
    logic [3:0] Q_reg;

    // Instantiate 4 D Flip-Flops with Set and Reset functionality
    always @(posedge clk or posedge reset)
    begin
        if (reset)
        begin
            Q_reg <= 4'b0;
        end
        else if (load)
        begin
            Q_reg <= data_in;
        end
    end

    always @*
    begin
        Q = Q_reg;
    end

    ///// Register behavior /////
    // Q_reg should only change on the rising edge of clk or on reset.
    reg_change: assert property (
        @(posedge clk) disable iff (!reset) Q_reg !== Q_reg
    );

    // Q_reg should be loaded with data_in when load is asserted.
    load_behavior: assert property (
        @(posedge clk) disable iff (!reset) (load == 1'b1) |-> (Q_reg == data_in)
    );

    // Q_reg should be reset to 0 when reset is asserted.
    reset_behavior: assert property (
        @(posedge clk) disable iff (!reset) reset |-> (Q_reg == 4'b0)
    );

    // Q should always reflect the current value of Q_reg.
    q_output: assert property (
        @(posedge clk) disable iff (!reset) Q == Q_reg
    );

    // Q_reg should not change when neither load nor reset is asserted.
    no_change: assert property (
        @(posedge clk) disable iff (!reset) (!load && !reset) |-> Q_reg == Q_reg
    );

    // Q_reg should not change when reset is asserted.
    reset_no_change: assert property (
        @(posedge clk) disable iff (!reset) reset |-> Q_reg == Q_reg
    );

    // Q_reg should not change when load is asserted but reset is not.
    load_no_change: assert property (
        @(posedge clk) disable iff (!reset) (load && !reset) |-> Q_reg == Q_reg
    );

    // Q_reg should not change when data_in is not changing.
    data_in_no_change: assert property (
        @(posedge clk) disable iff (!reset) data_in == data_in |-> Q_reg == Q_reg
    );

    // Q_reg should not change when clk is not rising edge.
    clk_no_change: assert property (
        @(posedge clk) disable iff (!reset) clk |-> Q_reg == Q_reg
    );

    // Q_reg should not change when load and reset are both asserted.
    load_reset_no_change: assert property (
        @(posedge clk) disable iff (!reset) (load && reset) |-> Q_reg == Q_reg
    );

endmodule
```