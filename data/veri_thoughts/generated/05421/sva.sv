module axi_data_fifo_v2_1_8_ndeep_srl_sva #(
    parameter C_FAMILY = "rtl",
    parameter integer C_A_WIDTH = 1
) (
    input logic                 CLK,
    input logic [C_A_WIDTH-1:0] A,
    input logic                 CE,
    input logic                 D,
    input logic                 Q
);

    localparam logic [C_A_WIDTH-1:0] ADDR_0 = '0;
    localparam logic [C_A_WIDTH-1:0] ADDR_1 = 1;

    property p_addr0_after_shift;
        logic d_first;
        @(posedge CLK)
            (CE, d_first = D) |=> ((A == ADDR_0) |-> (Q == d_first));
    endproperty

    property p_addr1_after_two_shifts;
        logic d_first;
        @(posedge CLK)
            (CE, d_first = D) ##1 CE |=> ((A == ADDR_1) |-> (Q == d_first));
    endproperty

    property p_addr1_after_two_shifts_and_hold;
        logic d_first;
        @(posedge CLK)
            (CE, d_first = D) ##1 CE ##1 !CE |=> ((A == ADDR_1) |-> (Q == d_first));
    endproperty

    // Address 0 returns the bit shifted in on the prior enabled cycle.
    check_addr0_after_shift: assert property (p_addr0_after_shift);

    // With CE low, Q holds when the selected address stays the same.
    check_hold_when_disabled: assert property (
        @(posedge CLK)
            !CE |=> ($stable(A) |-> $stable(Q))
    );

    // Address 1 returns the bit shifted in two enabled cycles earlier.
    check_addr1_after_two_shifts: assert property (p_addr1_after_two_shifts);

    // A disabled cycle does not disturb the data already shifted to address 1.
    check_addr1_after_two_shifts_and_hold: assert property (p_addr1_after_two_shifts_and_hold);

    generate
        if (C_A_WIDTH > 1) begin : gen_deeper_address_checks
            localparam logic [C_A_WIDTH-1:0] ADDR_2 = 2;
            localparam logic [C_A_WIDTH-1:0] ADDR_3 = 3;

            property p_addr2_after_three_shifts;
                logic d_first;
                @(posedge CLK)
                    (CE, d_first = D) ##1 CE ##1 CE |=> ((A == ADDR_2) |-> (Q == d_first));
            endproperty

            property p_addr3_after_four_shifts;
                logic d_first;
                @(posedge CLK)
                    (CE, d_first = D) ##1 CE ##1 CE ##1 CE |=> ((A == ADDR_3) |-> (Q == d_first));
            endproperty

            // Address 2 returns the bit shifted in three enabled cycles earlier.
            check_addr2_after_three_shifts: assert property (p_addr2_after_three_shifts);

            // Address 3 returns the bit shifted in four enabled cycles earlier.
            check_addr3_after_four_shifts: assert property (p_addr3_after_four_shifts);
        end
    endgenerate

endmodule