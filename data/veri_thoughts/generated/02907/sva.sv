module jmp_cond_sva (
    input logic [4:0] logic_flags,
    input logic [3:0] cond,
    input logic       is_cx,
    input logic [15:0] cx,
    input logic       jmp
);
    // Derived flag bits
    wire of = logic_flags[4];
    wire sf = logic_flags[3];
    wire zf = logic_flags[2];
    wire pf = logic_flags[1];
    wire cf = logic_flags[0];
    wire cx_zero = ~(|cx);

    ///// is_cx path /////
    // When is_cx and cond==0000, jmp equals cx_zero.
    check_is_cx_cond_0000: assert property (
        @(posedge $global_clock) (is_cx && (cond == 4'b0000)) |=> (jmp == cx_zero)
    );
    // When is_cx and cond==0001, jmp equals ~cx_zero.
    check_is_cx_cond_0001: assert property (
        @(posedge $global_clock) (is_cx && (cond == 4'b0001)) |=> (jmp == ~cx_zero)
    );
    // When is_cx and cond==0010, jmp equals zf & ~cx_zero.
    check_is_cx_cond_0010: assert property (
        @(posedge $global_clock) (is_cx && (cond == 4'b0010)) |=> (jmp == (zf & ~cx_zero))
    );
    // When is_cx and cond in {0011,0100..1111}, jmp equals ~zf & ~cx_zero.
    check_is_cx_cond_default: assert property (
        @(posedge $global_clock)
            (is_cx &&
             ((cond == 4'b0011) || (cond == 4'b0100) || (cond == 4'b0101) || (cond == 4'b0110) ||
              (cond == 4'b0111) || (cond == 4'b1000) || (cond == 4'b1001) || (cond == 4'b1010) ||
              (cond == 4'b1011) || (cond == 4'b1100) || (cond == 4'b1101) || (cond == 4'b1110) ||
              (cond == 4'b1111)))
        |=> (jmp == (~zf & ~cx_zero))
    );

    ///// !is_cx path /////
    // When !is_cx and cond==0000, jmp equals of.
    check_no_cx_cond_0000: assert property (
        @(posedge $global_clock) (!is_cx && (cond == 4'b0000)) |=> (jmp == of)
    );
    // When !is_cx and cond==0001, jmp equals ~of.
    check_no_cx_cond_0001: assert property (
        @(posedge $global_clock) (!is_cx && (cond == 4'b0001)) |=> (jmp == ~of)
    );
    // When !is_cx and cond==0010, jmp equals cf.
    check_no_cx_cond_0010: assert property (
        @(posedge $global_clock) (!is_cx && (cond == 4'b0010)) |=> (jmp == cf)
    );
    // When !is_cx and cond==0011, jmp equals ~cf.
    check_no_cx_cond_0011: assert property (
        @(posedge $global_clock) (!is_cx && (cond == 4'b0011)) |=> (jmp == ~cf)
    );
    // When !is_cx and cond==0100, jmp equals zf.
    check_no_cx_cond_0100: assert property (
        @(posedge $global_clock) (!is_cx && (cond == 4'b0100)) |=> (jmp == zf)
    );
    // When !is_cx and cond==0101, jmp equals ~zf.
    check_no_cx_cond_0101: assert property (
        @(posedge $global_clock) (!is_cx && (cond == 4'b0101)) |=> (jmp == ~zf)
    );
    // When !is_cx and cond==0110, jmp equals cf | zf.
    check_no_cx_cond_0110: assert property (
        @(posedge $global_clock) (!is_cx && (cond == 4'b0110)) |=> (jmp == (cf | zf))
    );
    // When !is_cx and cond==0111, jmp equals ~cf & ~zf.
    check_no_cx_cond_0111: assert property (
        @(posedge $global_clock) (!is_cx && (cond == 4'b0111)) |=> (jmp == (~cf & ~zf))
    );
    // When !is_cx and cond==1000, jmp equals sf.
    check_no_cx_cond_1000: assert property (
        @(posedge $global_clock) (!is_cx && (cond == 4'b1000)) |=> (jmp == sf)
    );
    // When !is_cx and cond==1001, jmp equals ~sf.
    check_no_cx_cond_1001: assert property (
        @(posedge $global_clock) (!is_cx && (cond == 4'b1001)) |=> (jmp == ~sf)
    );
    // When !is_cx and cond==1010, jmp equals pf.
    check_no_cx_cond_1010: assert property (
        @(posedge $global_clock) (!is_cx && (cond == 4'b1010)) |=> (jmp == pf)
    );
    // When !is_cx and cond==1011, jmp equals ~pf.
    check_no_cx_cond_1011: assert property (
        @(posedge $global_clock) (!is_cx && (cond == 4'b1011)) |=> (jmp == ~pf)
    );
    // When !is_cx and cond==1100, jmp equals sf ^ of.
    check_no_cx_cond_1100: assert property (
        @(posedge $global_clock) (!is_cx && (cond == 4'b1100)) |=> (jmp == (sf ^ of))
    );
    // When !is_cx and cond==1101, jmp equals sf XNOR of.
    check_no_cx_cond_1101: assert property (
        @(posedge $global_clock) (!is_cx && (cond == 4'b1101)) |=> (jmp == (sf ^~ of))
    );
    // When !is_cx and cond==1110, jmp equals zf | (sf ^ of).
    check_no_cx_cond_1110: assert property (
        @(posedge $global_clock) (!is_cx && (cond == 4'b1110)) |=> (jmp == (zf | (sf ^ of)))
    );
    // When !is_cx and cond==1111, jmp equals ~zf & (sf XNOR of).
    check_no_cx_cond_1111: assert property (
        @(posedge $global_clock) (!is_cx && (cond == 4'b1111)) |=> (jmp == (~zf & (sf ^~ of)))
    );
endmodule