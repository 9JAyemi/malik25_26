
module top_module (
    input clk,
    input reset,
    input control,
    input [3:0] a,
    input [3:0] b,
    output reg [3:0] out_add,
    output reg [3:0] out_sub,
    output reg [7:0] s,
    output overflow
);

// Sequential shift register module for storing the inputs
reg [3:0] reg_a, reg_b;
always @(posedge clk) begin
    if (reset) begin
        reg_a <= 4'b0000;
        reg_b <= 4'b0000;
    end else begin
        reg_a <= a;
        reg_b <= b;
    end
end

// Combinational circuit for addition and subtraction operations
wire [3:0] add_result, sub_result;
assign add_result = reg_a + reg_b;
assign sub_result = reg_a - reg_b;

// Carry look-ahead adder for addition and overflow detection
wire [4:0] add_carry;
assign add_carry = {1'b0, add_result} + {1'b0, reg_a} + {1'b0, reg_b};
assign overflow = add_carry[4];

// FSM for controlling the operation
reg [1:0] state;
parameter ADD = 2'b00, SUB = 2'b01;
always @(posedge clk) begin
    if (reset) begin
        state <= ADD;
    end else begin
        case (state)
            ADD: begin
                out_add <= add_result;
                s <= {1'b0, add_result};
                if (control) begin
                    state <= SUB;
                end
            end
            SUB: begin
                out_sub <= sub_result;
                s <= {1'b0, sub_result};
                if (!control) begin
                    state <= ADD;
                end
            end
        endcase
    end
end

endmodule