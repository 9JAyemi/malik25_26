module sync_counter (
    input clk_in,
    input rstn,
    output reg [3:0] count_out
);

    always @(posedge clk_in, negedge rstn) begin
        if (~rstn) begin
            count_out <= 4'b0;
        end else begin
            count_out <= count_out + 1;
        end
    end

endmodule