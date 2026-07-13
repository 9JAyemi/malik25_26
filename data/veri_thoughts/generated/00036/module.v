module clock_generator(
    input clk_in,
    output reg clk_out
);

reg [23:0] counter;

always @(posedge clk_in) begin
    if(counter == 24'd4_999_999) begin
        counter <= 0;
        clk_out <= ~clk_out;
    end else begin
        counter <= counter + 1;
    end
end

endmodule