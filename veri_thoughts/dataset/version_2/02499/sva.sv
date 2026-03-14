module acciones_to_bcd_sva (
    input logic clk,
    input logic rst,
    input logic [1:0] piso,
    input logic [1:0] accion,
    input logic puertas,
    input logic [3:0] BCD1,
    input logic [3:0] BCD2,
    input logic [3:0] BCD3,
    input logic [3:0] BCD4
);

    ///// BCD4 decodes piso when not in reset /////
    // piso==00 maps to BCD4=0001.
    check_bcd4_maps_piso_00: assert property (
        @(posedge clk) disable iff (rst) (piso == 2'b00) |-> (BCD4 == 4'b0001)
    );
    // piso==01 maps to BCD4=0010.
    check_bcd4_maps_piso_01: assert property (
        @(posedge clk) disable iff (rst) (piso == 2'b01) |-> (BCD4 == 4'b0010)
    );
    // piso==10 maps to BCD4=0011.
    check_bcd4_maps_piso_10: assert property (
        @(posedge clk) disable iff (rst) (piso == 2'b10) |-> (BCD4 == 4'b0011)
    );
    // piso==11 maps to BCD4=0100.
    check_bcd4_maps_piso_11: assert property (
        @(posedge clk) disable iff (rst) (piso == 2'b11) |-> (BCD4 == 4'b0100)
    );

    ///// BCD1 decodes accion when not in reset /////
    // accion==00 maps to BCD1=0000.
    check_bcd1_maps_accion_00: assert property (
        @(posedge clk) disable iff (rst) (accion == 2'b00) |-> (BCD1 == 4'b0000)
    );
    // accion==01 maps to BCD1=0101.
    check_bcd1_maps_accion_01: assert property (
        @(posedge clk) disable iff (rst) (accion == 2'b01) |-> (BCD1 == 4'b0101)
    );
    // accion==10 maps to BCD1=1000.
    check_bcd1_maps_accion_10: assert property (
        @(posedge clk) disable iff (rst) (accion == 2'b10) |-> (BCD1 == 4'b1000)
    );
    // accion==11 maps to BCD1=0000.
    check_bcd1_maps_accion_11: assert property (
        @(posedge clk) disable iff (rst) (accion == 2'b11) |-> (BCD1 == 4'b0000)
    );

    ///// BCD2 decodes puertas when not in reset /////
    // puertas==0 maps to BCD2=0111.
    check_bcd2_maps_puertas_0: assert property (
        @(posedge clk) disable iff (rst) (puertas == 1'b0) |-> (BCD2 == 4'b0111)
    );
    // puertas==1 maps to BCD2=0110.
    check_bcd2_maps_puertas_1: assert property (
        @(posedge clk) disable iff (rst) (puertas == 1'b1) |-> (BCD2 == 4'b0110)
    );

    ///// BCD3 behavior /////
    // When not in reset, BCD3 holds its value (no assignment in RTL).
    check_bcd3_stable_outside_reset: assert property (
        @(posedge clk) disable iff (rst) $stable(BCD3)
    );

endmodule