module dff_clear_reset(
    input clock,
    input clr,
    input clr_val,
    input d,
    output reg q
);

    always @(posedge clock) begin
        if (clr == 0) begin
            q <= 0;
        end else if (clr_val == 1) begin
            q <= d;
        end
    end

endmodule