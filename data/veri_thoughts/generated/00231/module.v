module shift_register (
    input clk,
    input reset,
    input shift_in,
    input shift,
    output reg [7:0] data_out
);

always @ (posedge clk, posedge reset) begin
    if (reset) begin
        data_out <= 8'b0;
    end else if (shift) begin
        data_out <= {data_out[6:0], 1'b0};
    end else begin
        data_out <= {data_out[6:0], shift_in};
    end
end

endmodule