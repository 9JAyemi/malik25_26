module burst_counter(
    input wire bclk,
    input wire [15:0] bus_ad,
    input wire [2:0] bus_a,
    input wire adv,
    input wire rw,
    input wire cs,
    output reg [15:0] measured_burst
);

    reg [15:0] burstcnt;   // counts the number of burst cycles
    reg [15:0] finalcnt;   // stores the number of burst cycles from the previous memory access operation
    reg activated;         // indicates whether the memory access operation is occurring
    reg activated_d;       // stores the value of activated from the previous clock cycle
    reg [15:0] bus_ad_r;   // stores the value of bus_ad from the previous clock cycle
    reg [2:0] bus_a_r;     // stores the value of bus_a from the previous clock cycle
    reg cs_r;              // stores the value of cs from the previous clock cycle
    reg rw_r;              // stores the value of rw from the previous clock cycle
    reg adv_r;             // stores the value of adv from the previous clock cycle
    
    always @(posedge bclk) begin
        // store the values of the input signals from the previous clock cycle
        bus_ad_r <= bus_ad;
        bus_a_r <= bus_a;
        cs_r <= cs;
        rw_r <= rw;
        adv_r <= adv;
        
        // check if the memory access operation is occurring
        if (cs_r && adv_r && ({bus_a_r, bus_ad_r[15:12]} == 7'h4_F)) begin
            activated <= 1'b1;
        end else if (!cs_r) begin
            activated <= 1'b0;
        end else begin
            activated <= activated;
        end
        
        // count the number of burst cycles during the memory access operation
        if (!activated) begin
            finalcnt <= burstcnt;
            burstcnt <= 16'h0;
        end else begin
            burstcnt <= burstcnt + 16'h1;
            finalcnt <= finalcnt;
        end
        
        // output the number of burst cycles on the falling edge of activated
        activated_d <= activated;
        if (activated_d & !activated) begin
            measured_burst <= finalcnt + 1'b1;
        end else begin
            measured_burst <= measured_burst;
        end
    end
    
endmodule