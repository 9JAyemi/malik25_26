// SVA checker for restoring_division_16bit
// Focus: correctness, sign rules, corner cases, and coverage.
// Bind this checker to the DUT.
module restoring_division_16bit_sva;

    // Helper functions
    function automatic signed [31:0] sext16(input signed [15:0] a);
        return {{16{a[15]}}, a};
    endfunction

    function automatic signed [16:0] abs16(input signed [15:0] a);
        // 17-bit safe absolute value (handles -32768 correctly)
        return a[15] ? -$signed({a[15], a}) : $signed({1'b0, a});
    endfunction

    // Core assertions (combinational)
    always @* begin
        // No X/Z on outputs when inputs are known
        if (!$isunknown({dividend, divisor}))
            assert (!$isunknown({quotient, remainder}))
                else $error("X/Z on outputs with known inputs");

        // Algebraic identity, remainder bound, and sign rules for legal divide
        if (!$isunknown({dividend, divisor, quotient, remainder}) && (divisor != 16'sd0)) begin
            // Dividend = Divisor*Quotient + Remainder (computed in 32-bit signed)
            assert (sext16(dividend) == ($signed(divisor) * $signed(quotient)) + sext16(remainder))
                else $error("D != S*Q + R");

            // |R| < |S|
            assert (abs16(remainder) < abs16(divisor))
                else $error("|R| >= |S|");

            // R sign == D sign (or R==0)
            assert ((remainder == 0) || (remainder[15] == dividend[15]))
                else $error("R sign != D sign");

            // Q sign == D^S (unless Q==0)
            assert ((quotient == 0) || (quotient[15] == (dividend[15] ^ divisor[15])))
                else $error("Q sign != D^S");
        end

        // Simple canonical cases
        if (!$isunknown({dividend, divisor}) && (dividend == 16'sd0))
            assert ((quotient == 16'sd0) && (remainder == 16'sd0))
                else $error("0/div case failed");

        if (!$isunknown({dividend, divisor}) && (divisor == 16'sd1))
            assert ((quotient == dividend) && (remainder == 16'sd0))
                else $error("div by +1 failed");

        if (!$isunknown({dividend, divisor}) && (divisor == -16'sd1) && (dividend != 16'sh8000))
            assert ((quotient == -dividend) && (remainder == 16'sd0))
                else $error("div by -1 (non-overflow) failed");

        if (!$isunknown({dividend, divisor}) && (divisor != 16'sd0) && (abs16(dividend) < abs16(divisor)))
            assert ((quotient == 16'sd0) && (remainder == dividend))
                else $error("|D|<|S| case failed");

        // Detect the signed overflow corner: -32768 / -1 (no 16-bit exact quotient exists)
        if ((divisor == -16'sd1) && (dividend == 16'sh8000))
            assert (0) else $error("Signed overflow: -32768 / -1");
    end

    // Coverage (hit key use-cases)
    always @* begin
        cover (divisor == 16'sd0);
        cover (dividend == 16'sd0);
        cover ((divisor != 16'sd0) && (remainder != 16'sd0));
        cover ((divisor != 16'sd0) && (dividend == divisor));
        cover ((divisor != 16'sd0) && (dividend == -divisor));
        cover ((divisor != 16'sd0) && (dividend[15] ^ divisor[15])); // opposite signs
        cover ((divisor != 16'sd0) && (~dividend[15] & ~divisor[15])); // both +
        cover ((divisor != 16'sd0) && ( dividend[15] &  divisor[15])); // both -
        cover (divisor == 16'sd1);
        cover (divisor == -16'sd1);
        cover ((divisor == -16'sd1) && (dividend == 16'sh8000)); // overflow case
    end

endmodule

bind restoring_division_16bit restoring_division_16bit_sva u_restoring_division_16bit_sva();