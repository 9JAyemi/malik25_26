
module xor_counter(
    input clk,
    input a,
    output reg out_comb_ff,
    output reg [1:0] out_counter
);

reg [1:0] counter;
reg out_ff;

always @(posedge clk) begin
    counter <= counter + 2'b01;
    out_counter <= counter;
end

always @* begin
    out_comb_ff <= a ^ out_ff;
end

always @(posedge clk) begin
    out_ff <= out_comb_ff;
end

endmodule