
module stratixv_output_alignment(
    input datain,
    input clk,
    input areset,
    input sreset,
    input [2:0] enaoutputcycledelay,
    input enaphasetransferreg,
    output dataout,
    output dffin,
    output dff1t,
    output dff2t,
    output dffphasetransfer
);

    parameter power_up = "low";
    parameter async_mode = "none";
    parameter sync_mode = "none";
    parameter add_output_cycle_delay = 0;
    parameter add_phase_transfer_reg = 0;

    reg [2:0] delay_counter;
    reg [2:0] phase_transfer_counter;
    reg delayed_data;
    reg dff1t_reg;
    reg dff2t_reg1;
    reg dff2t_reg2;
    reg dffphasetransfer_reg;

    always @(posedge clk or negedge areset) begin
        if(!areset) begin
            delay_counter <= 0;
            phase_transfer_counter <= 0;
            delayed_data <= 0;
            dff1t_reg <= 0;
            dff2t_reg1 <= 0;
            dff2t_reg2 <= 0;
            dffphasetransfer_reg <= 0;
        end else begin
            if(add_output_cycle_delay) begin
                if(delay_counter == enaoutputcycledelay) begin
                    delayed_data <= dffphasetransfer_reg;
                end else begin
                    delayed_data <= delayed_data;
                end
                delay_counter <= (delay_counter == enaoutputcycledelay) ? 0 : delay_counter + 1;
            end else begin
                delayed_data <= dffphasetransfer_reg;
            end

            if(add_phase_transfer_reg) begin
                if(phase_transfer_counter == 0) begin
                    dffphasetransfer_reg <= datain;
                end else begin
                    dffphasetransfer_reg <= dffphasetransfer_reg;
                end
                phase_transfer_counter <= (phase_transfer_counter == 7) ? 0 : phase_transfer_counter + 1;
            end else begin
                dffphasetransfer_reg <= datain;
            end

            dff1t_reg <= datain;
            dff2t_reg1 <= dff1t_reg;
            dff2t_reg2 <= dff1t_reg;
        end
    end

    assign dataout = delayed_data;
    assign dffin = datain;
    assign dff1t = dff1t_reg;
    assign dff2t = dff2t_reg1 & dff2t_reg2;
    assign dffphasetransfer = dffphasetransfer_reg;

endmodule