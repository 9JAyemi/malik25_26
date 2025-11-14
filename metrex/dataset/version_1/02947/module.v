
module ag6502_phase_shift(input baseclk, input phi_0, output reg phi_1);
    parameter DELAY = 1; // delay in waves of baseclk
    initial phi_1 = 0;
    integer cnt = 0;
    reg delayed_clk = 0;

    always @(posedge baseclk) begin
        if (phi_0 != phi_1) begin
            if (!cnt) begin
                delayed_clk <= 1'b1;
                cnt <= DELAY;
            end
            else cnt <= cnt - 1;
        end
        else begin
            if (cnt) begin
                cnt <= cnt - 1;
            end
            else
                delayed_clk <= 1'b0;
        end
    end

    always @(posedge baseclk) begin
        if (cnt) phi_1 <= phi_1;
        else if (delayed_clk) phi_1 <= ~phi_1;
        else phi_1 <= phi_0;
    end
endmodule