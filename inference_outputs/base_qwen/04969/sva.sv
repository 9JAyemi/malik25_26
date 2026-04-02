module comparator_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic reset,
    input logic enable,
    input logic load_A,
    input logic load_B,
    output logic EQ,
    output logic GT,
    output logic LT
);
    always @(posedge clk) disable iff (!reset) begin
        // Reset behavior: EQ, GT, LT should be 0 after reset
        reset_behavior: assert property (
            reset |-> (EQ == 1'b0) && (GT == 1'b0) && (LT == 1'b0)
        );

        // Enable behavior: EQ, GT, LT should be 0 when enable is 0
        enable_behavior: assert property (
            !enable |-> (EQ == 1'b0) && (GT == 1'b0) && (LT == 1'b0)
        );

        // Load_A behavior: A_reg should be updated when load_A is 1
        load_A_behavior: assert property (
            load_A |-> (A_reg == A)
        );

        // Load_B behavior: B_reg should be updated when load_B is 1
        load_B_behavior: assert property (
            load_B |-> (B_reg == B)
        );

        // Equality behavior: EQ should be 1 when A_reg == B_reg
        equality_behavior: assert property (
            A_reg == B_reg |-> EQ == 1'b1
        );

        // Greater than behavior: GT should be 1 when A_reg > B_reg
        greater_than_behavior: assert property (
            A_reg > B_reg |-> GT == 1'b1
        );

        // Less than behavior: LT should be 1 when A_reg < B_reg
        less_than_behavior: assert property (
            A_reg < B_reg |-> LT == 1'b1
        );
    end
endmodule