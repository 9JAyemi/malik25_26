
module delay_module (
    input clk,
    input A,
    input [3:0] delay_val,
    output reg X
);

reg [3:0] counter;

always @(posedge clk) begin
    if (counter == delay_val) begin
        X <= A;
    end else begin
        X <= X;
    end
    counter <= counter + 1;
end

endmodule
