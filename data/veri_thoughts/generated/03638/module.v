
module abs_val (
    input [3:0] num_in,
    input clk,
    input rst,
    output reg [3:0] abs_val_out
);

reg [3:0] neg_num;
reg [3:0] pos_num;

// 2's complement conversion
always @ (*) begin
    neg_num = ~num_in + 4'b1;
end

// Comparator to check if num_in is negative
wire is_neg = (num_in[3] == 1);

// Multiplexer to choose between num_in and neg_num
wire [3:0] mux_out;
assign mux_out = is_neg ? neg_num : num_in;

// Adder/subtractor to convert negative number to positive
always @ (*) begin
    pos_num = {1'b0, mux_out[2:0]} + 4'b1;
end

// Output register to synchronize output
always @(posedge clk, posedge rst) begin
    if (rst) begin
        abs_val_out <= 4'b0;
    end else begin
        abs_val_out <= pos_num[3:0];
    end
end

endmodule