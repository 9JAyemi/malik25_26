module up_counter(
    input clk,
    input reset_n,
    output reg [2:0] count
);

    always @(posedge clk or negedge reset_n) begin
        if (~reset_n) begin
            count <= 3'b0;
        end else begin
            count <= count + 1;
        end
    end

endmodule