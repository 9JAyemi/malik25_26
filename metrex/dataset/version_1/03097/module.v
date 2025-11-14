module ripple_add_sub (
    input clk,
    input reset,
    input [15:0] A,
    input [15:0] B,
    input select,
    output reg [15:0] S,
    output reg O
);

wire [15:0] B_complement;
wire [16:0] sum_subtract;
wire [16:0] sum_add;

assign B_complement = select ? ~B + 1'b1 : B; 
assign sum_add = {1'b0, A} + {1'b0, B_complement}; // Include initial carry 0
assign sum_subtract = {1'b0, A} + {1'b0, B_complement} + (select ? 16'b0 : 1'b1); // Add extra 1 only in addition mode

always @(posedge clk or posedge reset) begin
    if (reset) begin
        S <= 16'b0;
        O <= 1'b0;
    end else begin
        if (select) begin // subtraction mode
            S <= sum_subtract[15:0];
            O <= sum_subtract[16] ^ sum_subtract[15]; 
        end else begin // addition mode
            S <= sum_add[15:0];
            O <= sum_add[16]; // Carry out for addition
        end
    end
end

endmodule
