module simple_calculator_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic OP,
    input logic CLK,
    input logic RST,
    output logic [7:0] C
);

    reg [7:0] C_reg;

    always @(posedge CLK) begin
        if (RST) begin
            C_reg <= 8'b0;
        end else if (OP == 1) begin
            C_reg <= A - B;
        end else begin
            C_reg <= A + B;
        end
    end

    assign C = C_reg;

    ///// Reset behavior /////
    // At reset, C_reg must be driven to 0.
    reset_C_reg: assert property (
        @(posedge CLK) disable iff (!RST) RST |-> (C_reg == 8'b0)
    );

    ///// Operation behavior /////
    // When OP is 1, C_reg should be updated to A - B.
    operation_subtract: assert property (
        @(posedge CLK) disable iff (!RST) (OP == 1) |-> (C_reg == A - B)
    );

    // When OP is 0, C_reg should be updated to A + B.
    operation_add: assert property (
        @(posedge CLK) disable iff (!RST) (OP == 0) |-> (C_reg == A + B)
    );

endmodule