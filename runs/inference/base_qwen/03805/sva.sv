module Test6_assertions(
    input logic OE,
    inout logic [3:0] Z10
);
    wire [1:0] i;
    Test6a a (.OE(OE), .Z({Z10[1],Z10[0]})); // Z10[0] and Z10[1] swapped
    Test6a b (.OE(~OE), .Z({Z10[3],Z10[2]})); // Z10[2] and Z10[3] swapped

    // OE can only transition from HIGH to LOW when Z10[0] and Z10[1] are 10.
    oe_to_low_1: assert property (
        @(posedge OE) disable iff (!OE) $fell(OE) |-> (Z10[1] == 1'b1) && (Z10[0] == 1'b0)
    );

    // OE can only transition from HIGH to LOW when Z10[2] and Z10[3] are 10.
    oe_to_low_2: assert property (
        @(posedge OE) disable iff (!OE) $fell(OE) |-> (Z10[3] == 1'b1) && (Z10[2] == 1'b0)
    );

    // OE can only transition from LOW to HIGH when Z10[0] and Z10[1] are 01.
    oe_to_high_1: assert property (
        @(posedge OE) disable iff (!OE) $rose(OE) |-> (Z10[1] == 1'b0) && (Z10[0] == 1'b1)
    );

    // OE can only transition from LOW to HIGH when Z10[2] and Z10[3] are 01.
    oe_to_high_2: assert property (
        @(posedge OE) disable iff (!OE) $rose(OE) |-> (Z10[3] == 1'b0) && (Z10[2] == 1'b1)
    );

    // Z10[0] and Z10[1] are swapped in module a.
    swap_a: assert property (
        @(posedge OE) disable iff (!OE) Z10[0] |-> Z10[1] == a.Z
    );

    // Z10[2] and Z10[3] are swapped in module b.
    swap_b: assert property (
        @(posedge OE) disable iff (!OE) Z10[2] |-> Z10[3] == b.Z
    );

    // Z10[0] and Z10[1] are driven by module a.
    drive_a: assert property (
        @(posedge OE) disable iff (!OE) Z10[0] |-> a.Z == 2'b01
    );

    // Z10[2] and Z10[3] are driven by module b.
    drive_b: assert property (
        @(posedge OE) disable iff (!OE) Z10[2] |-> b.Z == 2'b10
    );

    // OE can only be HIGH when Z10[0] and Z10[1] are 01 or 10.
    oe_valid_1: assert property (
        @(posedge OE) disable iff (!OE) OE |-> (Z10[1] == 1'b0) && (Z10[0] == 1'b1)
    );

    // OE can only be HIGH when Z10[0] and Z10[1] are 01 or 10.
    oe_valid_2: assert property (
        @(posedge OE) disable iff (!OE) OE |-> (Z10[1] == 1'b1) && (Z10[0] == 1'b0)
    );

    // OE can only be HIGH when Z10[2] and Z10[3] are 01 or 10.
    oe_valid_3: assert property (
        @(posedge OE) disable iff (!OE) OE |-> (Z10[3] == 1'b0) && (Z10[2] == 1'b1)
    );

    // OE can only be HIGH when Z10[2] and Z10[3] are 01 or 10.
    oe_valid_4: assert property (
        @(posedge OE) disable iff (!OE) OE |-> (Z10[3] == 1'b1) && (Z10[2] == 1'b0)
    );
endmodule