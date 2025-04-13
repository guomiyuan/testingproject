package com.fastaccess.tfl.helper.combinatorial;

import com.fastaccess.tfl.helper.DateHelper;
import com.fastaccess.tfl.helper.DateHelper.DateFormats;
import org.junit.Test;
import org.junit.BeforeClass;

import java.util.TimeZone;
import java.util.Locale;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Date;

import static org.junit.Assert.*;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.*;



public class DateCombinatorialTest {

    @BeforeClass
    public static void setUpLocale() {
        Locale.setDefault(Locale.ENGLISH);
        TimeZone.setDefault(TimeZone.getTimeZone("UTC"));
    }

    @Test
    public void testGetDesiredFormat() {
        assertEquals("1970-01-01", DateHelper.getDesiredFormat(DateFormats.D_YYYYMMDD, 0L));
        assertEquals("01/01/1970", DateHelper.getDesiredFormat(DateFormats.S_DDMMYYYY, 0L));
        assertTrue(DateHelper.getDesiredFormat(DateFormats.D_DDMMYYYYHHMMA, 0L).contains("01-01-1970"));
        assertEquals("12:00AM", DateHelper.getDesiredFormat(DateFormats.HHMMA, 0L).replace(" ", ""));
        assertEquals("70-01-01", DateHelper.getDesiredFormat(DateFormats.D_YYMMDD, 0L));

        assertEquals("1970-01-01", DateHelper.getDesiredFormat(DateFormats.D_YYYYMMDD, 1L));
        assertEquals("01/01/1970", DateHelper.getDesiredFormat(DateFormats.S_DDMMYYYY, 1L));
        assertTrue(DateHelper.getDesiredFormat(DateFormats.D_DDMMYYYYHHMMA, 1L).contains("01-01-1970"));
        assertEquals("12:00AM", DateHelper.getDesiredFormat(DateFormats.HHMMA, 1L).replace(" ", ""));
        assertEquals("70-01-01", DateHelper.getDesiredFormat(DateFormats.D_YYMMDD, 1L));

        assertEquals("2023-01-01", DateHelper.getDesiredFormat(DateFormats.D_YYYYMMDD, 1672531200000L));
        assertEquals("01/01/2023", DateHelper.getDesiredFormat(DateFormats.S_DDMMYYYY, 1672531200000L));
        assertTrue(DateHelper.getDesiredFormat(DateFormats.D_DDMMYYYYHHMMA, 1672531200000L).contains("01-01-2023"));
        assertEquals("12:00AM", DateHelper.getDesiredFormat(DateFormats.HHMMA, 1672531200000L).replace(" ", ""));
        assertEquals("23-01-01", DateHelper.getDesiredFormat(DateFormats.D_YYMMDD, 1672531200000L));

        assertNotNull(DateHelper.getDesiredFormat(DateFormats.D_YYYYMMDD, -1L));
        assertNotNull(DateHelper.getDesiredFormat(DateFormats.S_DDMMYYYY, -1L));
        assertNotNull(DateHelper.getDesiredFormat(DateFormats.D_DDMMYYYYHHMMA, -1L));
        assertNotNull(DateHelper.getDesiredFormat(DateFormats.HHMMA, -1L));
        assertNotNull(DateHelper.getDesiredFormat(DateFormats.D_YYMMDD, -1L));

        assertNotNull(DateHelper.getDesiredFormat(DateFormats.D_YYYYMMDD, Long.MAX_VALUE));
        assertNotNull(DateHelper.getDesiredFormat(DateFormats.S_DDMMYYYY, Long.MAX_VALUE));
        assertNotNull(DateHelper.getDesiredFormat(DateFormats.D_DDMMYYYYHHMMA, Long.MAX_VALUE));
        assertNotNull(DateHelper.getDesiredFormat(DateFormats.HHMMA, Long.MAX_VALUE));
        assertNotNull(DateHelper.getDesiredFormat(DateFormats.D_YYMMDD, Long.MAX_VALUE));
    }

    @Test
    public void testParseDate() {
        assertNotEquals(0L, DateHelper.parseDate("2025-07-15", DateFormats.D_YYYYMMDD));
        assertNotEquals(0L, DateHelper.parseDate("15/07/2025", DateFormats.S_DDMMYYYY));

        assertEquals(0L, DateHelper.parseDate("invalid-date", DateFormats.D_DDMMYYYYHHMMA));
        assertEquals(0L, DateHelper.parseDate("invalid-date", DateFormats.HHMMA));
        assertEquals(0L, DateHelper.parseDate("invalid-date", DateFormats.S_YYYYMMDDHHMMSSA));

        assertNotEquals(0L, DateHelper.parseDate("2020-02-29", DateFormats.D_YYYYMMDD));
        assertNotEquals(0L, DateHelper.parseDate("29/02/2020", DateFormats.S_DDMMYYYY));

        assertEquals(0L, DateHelper.parseDate("", DateFormats.S_DDMMYYYY));
        assertEquals(0L, DateHelper.parseDate("", DateFormats.D_DDMMYYYYHHMMA));
        assertEquals(0L, DateHelper.parseDate("", DateFormats.HHMMA));
        assertEquals(0L, DateHelper.parseDate("", DateFormats.S_YYYYMMDDHHMMSSA));

        //assertEquals(0L, DateHelper.parseDate(null, DateFormats.S_DDMMYYYY));
        //assertEquals(0L, DateHelper.parseDate(null, DateFormats.D_DDMMYYYYHHMMA));
        //assertEquals(0L, DateHelper.parseDate(null, DateFormats.HHMMA));
        //assertEquals(0L, DateHelper.parseDate(null, DateFormats.S_YYYYMMDDHHMMSSA));

        assertEquals(0L, DateHelper.parseDate("invalid-date", DateFormats.D_YYYYMMDD));
        assertEquals(0L, DateHelper.parseDate("invalid-date", DateFormats.S_DDMMYYYY));
        assertEquals(0L, DateHelper.parseDate("", DateFormats.D_YYYYMMDD));

    }

	@Test
	public void testGetDaysBetweenTwoDate() {
		Long result1 = DateHelper.getDaysBetweenTwoDate("01/04/2025", "09/04/2025", DateFormats.S_DDMMYYYY);
		assertNotNull("Normal date calculation should not return null", result1);
		assertEquals("01/04 to 09/04 should have 8 days difference", 8L, Math.abs(result1.longValue()));

		Long result2 = DateHelper.getDaysBetweenTwoDate("09/04/2025", "09/04/2025", DateFormats.S_DDMMYYYY);
		assertNotNull("Same date calculation should not return null", result2);
		assertEquals("Same dates should return 0 days difference", 0L, result2.longValue());

		Long result3 = DateHelper.getDaysBetweenTwoDate("08/04/2025", "09/04/2025", DateFormats.S_DDMMYYYY);
		assertNotNull("1-day interval calculation should not return null", result3);
		assertEquals("08/04 to 09/04 should have 1 day difference", 1L, Math.abs(result3.longValue()));

		Long result4 = DateHelper.getDaysBetweenTwoDate("invalid_date", "09/04/2025", DateFormats.S_DDMMYYYY);
		assertNull("Invalid date should return null", result4);

		Long result5 = DateHelper.getDaysBetweenTwoDate("13/09/2025", "09/04/2025", DateFormats.S_DDMMYYYY);
		assertNotNull("Valid dates should not return null", result5);

		// Verify date order handling
		Long result6 = DateHelper.getDaysBetweenTwoDate("09/04/2025", "01/04/2025", DateFormats.S_DDMMYYYY);
		assertNotNull("Date order should not affect result", result6);
		assertEquals("09/04 to 01/04 should have 8 days difference", 8L, Math.abs(result6.longValue()));
	}
	
	
	// Add new test cases to improve mutation score and jacoco score
    @Test
    public void testParseAnyDate() {
        assertNotEquals(0L, DateHelper.parseAnyDate("2025-07-15")); 
        assertNotEquals(0L, DateHelper.parseAnyDate("15/07/2025")); 
        assertEquals(0L, DateHelper.parseAnyDate("invalid-date")); 
        assertEquals(0L, DateHelper.parseAnyDate("")); 
    }

    @Test
    public void testGetHoursBetweenTwoDate() {
        Long result1 = DateHelper.getHoursBetweenTwoDate("01/04/2025", "09/04/2025", DateFormats.S_DDMMYYYY);
        assertNotNull(result1);
        assertEquals(192L, Math.abs(result1.longValue())); // 8 days = 192 hours

        Long result2 = DateHelper.getHoursBetweenTwoDate("invalid_date", "09/04/2025", DateFormats.S_DDMMYYYY);
        assertNull(result2);
    }

    @Test
    public void testGetMinutesBetweenTwoDates() {
        Long result1 = DateHelper.getMinutesBetweenTwoDates("01/04/2025", "02/04/2025", DateFormats.S_DDMMYYYY);
        assertNotNull(result1);
        assertEquals(1440L, Math.abs(result1.longValue())); // 1 day = 1440 minutes

        Long result2 = DateHelper.getMinutesBetweenTwoDates("invalid_date", "09/04/2025", DateFormats.S_DDMMYYYY);
        assertNull(result2);
    }

    @Test
    public void testGetTomorrow() {
        String today = DateHelper.getToday();
        String tomorrow = DateHelper.getTomorrow();
        assertNotNull(tomorrow);
        
        //  Verify that tomorrow is indeed today + 1 day
        Long daysBetween = DateHelper.getDaysBetweenTwoDate(today, tomorrow, DateFormats.S_DDMMYYYY);
        assertEquals(1L, Math.abs(daysBetween.longValue()));
    }
	
    @Test
    public void testGetDateOnly() {
        //Test String Version
        long dateOnly = DateHelper.getDateOnly("15/07/2025");
        assertNotEquals(0L, dateOnly);
        
        // Testing for invalid dates
        assertEquals(0L, DateHelper.getDateOnly("invalid-date"));
        
        // Test long version
        String dateStr = DateHelper.getDateOnly(dateOnly);
        assertEquals("15/07/2025", dateStr);
    }

	@Test
	public void testGetDateAndTime() {
		// Test long version
		String dateTime = DateHelper.getDateAndTime(0L);
		assertTrue(dateTime.contains("01/01/1970"));
		assertTrue(dateTime.contains("12:00 AM"));

		// Use long for consistency testing
		long now = System.currentTimeMillis();
		String expected = new SimpleDateFormat("dd/MM/yyyy, hh:mm a", Locale.getDefault()).format(new Date(now));
		String result = DateHelper.getDateAndTime(now);
		assertEquals(expected, result);

		try {
			DateHelper.getDateAndTime("invalid-time"); 
			fail("Expected IllegalArgumentException");
		} catch (IllegalArgumentException e) {
		}
	}
	
    @Test
    public void testGetTimeOnly() {
        String timeOnly = DateHelper.getTimeOnly(0L);
        assertEquals("12:00 AM", timeOnly);
    }

    @Test
    public void testGetTodayWithTime() {
        String todayWithTime = DateHelper.getTodayWithTime();
        assertNotNull(todayWithTime);
        assertTrue(todayWithTime.matches("\\d{2}/\\d{2}/\\d{4} \\d{2}:\\d{2}:\\d{2}"));
    }

    @Test
    public void testGetToday() {
        String today = DateHelper.getToday();
        assertNotNull(today);
        assertTrue(today.matches("\\d{2}/\\d{2}/\\d{4}"));
    }

    @Test
    public void testGetDateFromDays() {
        String dateIn2Days = DateHelper.getDateFromDays(2);
        assertNotNull(dateIn2Days);
        
        String dateInMinus2Days = DateHelper.getDateFromDays(-2);
        assertNotNull(dateInMinus2Days);
    }

    @Test
    public void testGetDesiredFormatCurrentDate() {
        String currentDate = DateHelper.getDesiredFormat(DateFormats.D_YYYYMMDD);
        assertNotNull(currentDate);
        assertTrue(currentDate.matches("\\d{4}-\\d{2}-\\d{2}"));
    }

    @Test
    public void testEdgeCases() {
        // Test Long.MIN_VALUE
        assertNotNull(DateHelper.getDesiredFormat(DateFormats.D_YYYYMMDD, Long.MIN_VALUE));
        
        // Testing for an empty string
        assertEquals(0L, DateHelper.parseDate("", DateFormats.D_YYYYMMDD));
        
        // Testing for leap years
        assertNotEquals(0L, DateHelper.parseDate("29/02/2020", DateFormats.S_DDMMYYYY));
    }
	
	@Test
	public void testConstructor() {
		DateHelper helper = new DateHelper();
		assertNotNull(helper); // Make sure the constructor is available
	}
	
	
}