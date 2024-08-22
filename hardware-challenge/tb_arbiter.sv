// Cycle through each possible input
    // Do in ascending order of priority
    // Also checks illegal transitions
    // There's a better way to do this probably
    initial begin
        r = 3'b0;
        #110
        forever begin
            r = 3'b111;
            #25
            r = 3'b000;
            #25
            r = 3'b110;
            #25
            r = 3'b000;
            #25
            r = 3'b101;
            #25
            r = 3'b000;
            #25
            r = 3'b100;
            #25
            // Next two test cases check for illegal transitions
            r = 3'b110;
            #25
            r = 3'b101;
            #25
            r = 3'b000;
            #25
            r = 3'b011;
            #25
            r = 3'b000;
            #25
            r = 3'b010;
            #25
            // Next two test cases check for illegal transitions
            r = 3'b110;
            #25
            r = 3'b011;
            #25
            r = 3'b000;
            #25
            r = 3'b001;
            #25
            // Next two test cases check for illegal transitions
            r = 3'b011;
            #25
            r = 3'b101;
            $stop();
        end
    end