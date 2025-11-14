module openhmc_sync_fifo_reg_stage #(parameter DWIDTH = 8)(
    input wire clk,
    input wire res_n,
    input wire [DWIDTH-1:0] d_in,
    input wire [DWIDTH-1:0] d_in_p,
    input wire p_full,
    input wire n_full,
    input wire si,
    input wire so,
    output reg full,
    output reg [DWIDTH-1:0] d_out
);

    wire en, muxi;

    assign en = (si & so & full)                // so and si, shift through
                | (si & ~so & ~full && n_full)  // shift in new value
                | (~si & so & p_full);          // shift through

    assign muxi = (si & ~so) | (si & so & ~p_full & full);

    always @ (posedge clk or negedge res_n) begin
        if (!res_n) begin
            full <= 1'b0;
            d_out <= {DWIDTH{1'b0}};
        end else begin
            if (en) begin
                if (muxi) begin
                    d_out <= d_in;      // enter new value when enabled
                end else begin
                    d_out <= d_in_p;    // shift through
                end
            end

            full <= (full & si)             // stay full while si to other stage
                    | (full & ~si & ~so)    // hold full
                    | (~si & so & p_full)   // keep full as long as prev stage is full
                    | (si & ~so & n_full);  // fill this stage by si
        end
    end

endmodule