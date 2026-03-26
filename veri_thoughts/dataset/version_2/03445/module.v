
module address_to_value (
    input [14:0] address,
    input clock,
    output reg [11:0] q
);

    always @(posedge clock) begin
        if (address >= 4096) begin
            q <= 12'b0;
        end else begin
            q <= address[11:0];
        end
    end

endmodule