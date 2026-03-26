
module binary_counter(
    input clk, rst_n,
    output reg [3:0] count
);

    always @(posedge clk or negedge rst_n) begin
        if(!rst_n) begin
            count <= 4'b0000; // reset to 0
        end else begin
            count <= count + 1; // increment
        end
    end

endmodule